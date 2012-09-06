
open Lexing
module S = Settings

let pr = Printf.printf
let spr = Printf.sprintf


(***** Command-line options ***************************************************)

let parseOnly = ref false
let doRaw     = ref false
let srcFiles  = ref []

let usage = "\n./system-d [options] [src_file]\n"

let argSpecs = [
  ("-parseOnly", Arg.Set parseOnly, "");
  ("-strictWarn", Arg.Bool (fun b -> S.strictWarn := b),
               "     <bool> treat warnings as errors (default is true)");
  ("-raw", Arg.Set doRaw,
        "            don't a-normalize or insert prelude");
  ("-fast", Arg.Unit (fun () ->
              Cnf.checkConversion := false;
              Log.printToStdout := false;
              Log.printToLog := false;
              S.checkWfSynthesis := false;
              ()),
         "           don't check CNF conversion, ");
  ("-checkCNF", Arg.Set Cnf.checkConversion,
             "       check CNF conversion");
  ("-printAllTypes", Arg.Set S.printAllTypes,
                  "  default is just top-level definitions");
  ("-printFullQuick", Arg.Clear S.printShortQuick,
                   " don't abbreviate quick types");
  ("-meet", Arg.Set Sub.doMeet,
         "           use meet to combine type terms");
  ("-join", Arg.Int (fun i -> Sub.maxJoinSize := i),
         "           <int> max size for CanFlow (default is 1, i.e. no join)");
(*
  ("-useLA", Arg.Unit (fun () -> S.useTheoryLA := true),
          "          use theory of linear arithmetic");
*)
  ("-tryAllBoxes", Arg.Set S.tryAllBoxesHack,
                "    try all boxes, in case typeTerms misses some");
  ("-doFalseChecks", Arg.Set S.doFalseChecks,
                  "  do false checks, which is a _de-optimization_");
  ("-noQuickTypes", Arg.Clear S.quickTypes,
               "     do all subtyping with logical queries");
  ("-djs", Arg.Set S.djsMode,
        "            Dependent JavaScript");
(*
  ("-varLifting", Arg.Bool (fun b -> S.doVarLifting := b),
               "     <bool> (default is false)");
  ("-implicitGlobal", Arg.Bool (fun b -> S.doImplicitGlobal := b),
                   " <bool> (default is false)");
  ("-argsArray", Arg.Set S.doArgsArray,
              "      desugar lambdas/calls with arguments tuple");
*)
  ("-augmentHeaps", Arg.Bool (fun b -> S.augmentHeaps := b),
                 "   <bool> tc will insert omitted locations (default true)");
(*
  ("-greedyThaws", Arg.Set S.greedyThaws,
                "    desugaring inserts thaw/freeze greedily around weak locs");
*)
  ("-assistCtor", Arg.Set S.assistCtor,
               "     desugaring wraps annotation around calls to ctor funcs");
]

let anonArgFun s =
  srcFiles := !srcFiles @ [s]


(******************************************************************************)

let checkSuffix s =
  let check suf = Str.string_match (Str.regexp (spr ".*%s$" suf)) s 0 in
  let warn suf s =
    Log.warn (Utils.yellowString
      (spr "File has suffix %s. Did you mean to be in %s mode?" suf s)) in
  if !doRaw then ()
  (* else if check ".ml" && !S.langMode <> S.D then warn ".ml" "D" *)
  (* else if check ".dref" && !S.langMode <> S.DREF then warn ".dref" "DREF" *)
  else if check ".js" && !S.djsMode = false then warn ".js" "DJS"
  else ()

let makeAbsolute f =
  if f.[0] = '/' then f else Unix.getcwd () ^ "/" ^ f


(***** Parse System !D ********************************************************)

let string_of_position (p, e) = 
  Format.sprintf "%s:%d:%d-%d" p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol)
    (e.pos_cnum - e.pos_bol)

(* rkc: handling position info similar to Lambdajs.parse_lambdajs and
   Lambdajs_env.parse_env *)
let doParse start_production name =
  let lexbuf = Lexing.from_channel (open_in name) in
  let strPos () = string_of_position (lexbuf.lex_curr_p, lexbuf.lex_curr_p) in
    try begin
      (* Set the correct filename in lexbuf (for source-tracking). *)
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with
                               pos_fname = name; pos_lnum = 1 };
      start_production LangLexer.token lexbuf
    end with
      | Failure s when String.length s >= 13 &&
                       String.sub s 0 13 = "Lex: bad char" ->
          Log.printParseErr (spr "%s\n\nat %s" s (strPos ()))
      | Failure "lexing: empty token" ->
          Log.printParseErr (spr "lexical error\n\nat %s" (strPos ()))
      | Lang.Parse_error(s) ->
          Log.printParseErr (spr "at %s\n\n%s" (strPos ()) s)
      | Parsing.Parse_error _  (* thrown when using ocamlyacc *)
      | LangParser2.Error ->   (* thrown when using menhir *)
          Log.printParseErr
            (spr "unexpected token [%s]\n\nat %s" (lexeme lexbuf) (strPos ()))

let parsePrelude f =
  fun e ->
    let prelude = doParse LangParser2.prelude f in
    Lang.ELoadedSrc (f, prelude e)

let anfAndAddPrelude e =
  if !doRaw then
    Anf.coerce e
  else
    let basics = parsePrelude (S.prim_dir ^ "basics.dref") in
    let objects = parsePrelude (S.prim_dir ^ "objects.dref") in
    let e =
      if !S.djsMode then
        let natives = parsePrelude (S.prim_dir ^ "js_natives.dref") in
        basics (objects (natives e))
      else
        basics (objects e)
    in
    let e = Anf.anfExp e in
    let _ = Anf.printAnfExp e in
    e

let rec expandProg originalF = function
  | Lang.ELoadSrc(f',e) ->
      let prelude = parsePrelude (S.djs_dir ^ f') in
      prelude (expandProg originalF e)
  | e ->
      Lang.ELoadedSrc (originalF, e)

let parseSystemDref () =
  let e =
    match !srcFiles with
      | []  -> Lang.EVal (LangUtils.vStr "no source file")
      | [f] -> let f = makeAbsolute f in
               (checkSuffix f; expandProg f (doParse LangParser2.prog f))
      | _   -> (pr "%s" usage; Log.terminate ())
  in
  anfAndAddPrelude e


(***** Parsing DJS ************************************************************)

let parseJStoEJS f =
  Exprjs_syntax.from_javascript
    (JavaScript.parse_javascript_from_channel (open_in f) f)

let dummyEJS =
  Exprjs_syntax.ConstExpr
    (LangUtils.pos0, JavaScript_syntax.CString "no source file")

let doParseDJS fo =
  try
    let prog = match fo with Some(f) -> parseJStoEJS f | None -> dummyEJS in
(*
    let f_pre = S.prim_dir ^ "prelude.js" in
    let ejs_pre = parseJStoEJS f_pre in
    DjsDesugar2.desugar (DjsDesugar2.makeFlatSeq ejs_pre prog)
*)
    DjsDesugar2.desugar prog
  with Failure(s) ->
    if Utils.strPrefix s "parse error" || Utils.strPrefix s "lexical error"
    then Log.printParseErr s
    else failwith s

let parseDJS () =
  let e =
    match !srcFiles with
      | []  -> doParseDJS None
      | [f] -> (checkSuffix f; doParseDJS (Some f))
      | _   -> (pr "%s" usage; Log.terminate ())
  in
  anfAndAddPrelude e


(***** Main *******************************************************************)

let _ = 

  Arg.parse argSpecs anonArgFun usage;
  let e = if !S.djsMode then parseDJS () else parseSystemDref () in
  if !parseOnly then begin
    pr "\n%s\n" (Utils.greenString "PARSE SUCCEEDED");
    exit 0
  end;

  if !Sub.doMeet then failwith "meet not implemented in dref/djs";
  if !Sub.maxJoinSize > 1 then failwith "join not implemented in dref/djs";

  Zzz.emitPreamble ();
  TcDref3.typecheck e;
  BNstats.print (open_out (S.out_dir ^ "stats.txt")) "";
  ()
  
