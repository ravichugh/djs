
open Lexing
module S = Settings

let pr = Printf.printf
let spr = Printf.sprintf


(***** Command-line options ***************************************************)

let doRaw     = ref false
let srcFiles  = ref []

let usage = "\nUsage: ./system-dref [options] [src_file]\n"

let argSpecs = [
  ("-djs", Arg.Set S.djsMode,
        "            process Dependent JavaScript file");
  ("-raw", Arg.Set doRaw,
        "            process A-normal System !D file directly with no prelude");
]

let argSpecs = (* most options are defined in ParseUtils *)
  argSpecs @ ParseUtils.argSpecs

let anonArgFun s =
  srcFiles := !srcFiles @ [s]


(******************************************************************************)

let checkSuffix s =
  let check suf = Str.string_match (Str.regexp (spr ".*%s$" suf)) s 0 in
  let warn suf s =
    Log.warn (Utils.yellowString
      (spr "File has suffix %s. Did you mean to be in %s mode?" suf s)) in
  if !doRaw then ()
  else if check ".dref" && !S.djsMode then warn ".dref" "DREF"
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
  if !S.parseOnly then begin
    pr "\n%s\n" (Utils.greenString "PARSE SUCCEEDED");
    exit 0
  end;
  Zzz.emitPreamble ();
  TcDref3.typecheck e;
  BNstats.print (open_out (S.out_dir ^ "stats.txt")) "";
  ()
  
