
open Lang
open LangUtils

module E = Exprjs_syntax
module J = JavaScript_syntax
module L = Lambdajs_syntax

module IdMap = Prelude.IdMap
module IdSet = Prelude.IdSet
module IdSetExt = Prelude.IdSetExt

module StrSet = Utils.StrSet


(* these should match the ones in js_natives.dref *)
let predefinedVars = ["undefined"; "Infinity"; "NaN"; "isArray"]


(***** Check variable scopes **************************************************)

exception NeedVarLifting of Prelude.id * Prelude.id
exception NeedImplicitGlobal of Prelude.id * Prelude.id

let rec foo curFunc lexScope varScope = function
  | E.VarExpr (_, x) ->
      if        not (IdSet.mem x lexScope) &&
                IdSet.mem x varScope &&
                true (* not (!Settings.doVarLifting) *) then
                  raise (NeedVarLifting (curFunc, x))
      else if   not (IdSet.mem x lexScope) &&
                not (IdSet.mem x varScope) &&
                true (* not (!Settings.doImplicitGlobal) *) then
                  raise (NeedImplicitGlobal (curFunc, x))
      else      lexScope
  | E.FuncExpr (_, l, e) ->
      let env = E.locals e in
      let newLexScope  =
        List.fold_left (fun acc x -> IdSet.add x acc) lexScope l in
      let _ = foo (spr "%s.ANON_FUNC" curFunc) newLexScope env e in
      lexScope
  | E.FuncStmtExpr (_, f, l, e) ->
      let env = E.locals e in
      let newLexScope  =
        IdSet.add f
          (List.fold_left (fun acc x -> IdSet.add x acc) lexScope l) in
      let _ = foo (spr "%s.ANON_FUNC" curFunc) newLexScope env e in
      newLexScope
  | E.ConstExpr _
  | E.ThisExpr _ -> lexScope
  | E.ArrayExpr (_, es) -> fooFold curFunc lexScope varScope es
  | E.ObjectExpr (_, ps) ->
      let es = List.map (fun (_,_,e) -> e) ps in
      fooFold curFunc lexScope varScope es
  (* TODO look at this and djsLite/fail/fail06.js *)
(*
  | E.IdExpr _ -> failwith "checkVars idexpr"
*)
  (* TODO 3/15 not sure what difference is between IdExpr and VarExpr *)
  | E.IdExpr(p,x) -> foo curFunc lexScope varScope (E.VarExpr(p,x))
  | E.NewExpr (_, c, args) ->
      let _ = fooIter curFunc lexScope varScope args in
      lexScope
  | E.PrefixExpr (_, _, e)
  | E.ThrowExpr (_, e)
  | E.HintExpr (_, _, e) -> foo curFunc lexScope varScope e
  | E.BracketExpr (_, e1, e2)
  | E.InfixExpr (_, _, e1, e2) -> fooFold curFunc lexScope varScope [e1;e2]
  (* 3/31 TODO need to add k into scope *)
  | E.ForInExpr (_, _, e1, e2)
  | E.WhileExpr (_, e1, e2)
  | E.DoWhileExpr (_, e1, e2) ->
      (* shouldn't accumulate lexScope, right? *)
      let _ = fooIter curFunc lexScope varScope [e1;e2] in
      lexScope
  | E.IfExpr (_, e1, e2, e3) ->
      let _ = fooIter curFunc lexScope varScope [e1;e2;e3] in
      lexScope
  | E.AssignExpr (_, l, e) ->
      foo curFunc (fooLv curFunc lexScope varScope l) varScope e
  | E.AppExpr (_, f, args) -> fooFold curFunc lexScope varScope (f::args)
  | E.LetExpr (_, x, e1, e2) -> 
      (* rkc: not sure if x needs to be added or not *)
      fooFold curFunc (IdSet.add x lexScope) varScope [e1;e2]
  | E.SeqExpr (_, e1, e2) ->
      fooFold curFunc lexScope varScope [e1;e2]
  | E.LabelledExpr (_, _, e) -> foo curFunc lexScope varScope e
  | E.BreakExpr (_, _, e) -> foo curFunc lexScope varScope e
  | E.VarDeclExpr (_, x, e) ->
      IdSet.add x (foo curFunc lexScope varScope e)
  | E.TryCatchExpr (_, e1, _, e2) -> (* TODO catch bound identifiers *)
      fooFold curFunc lexScope varScope [e1;e2]
  | E.TryFinallyExpr (_, e1, e2) ->
      fooFold curFunc lexScope varScope [e1;e2]
(*
  | E.FuncStmtExpr (_, f, _, _) -> IdSet.singleton f
*)

and fooLv curFunc lexScope varScope = function
    E.VarLValue _ -> lexScope
  | E.PropLValue (_, e1, e2) -> fooFold curFunc lexScope varScope [e1;e2]

(* chain scopes together *)
and fooFold curFunc lexScope varScope es =
  List.fold_left (fun acc -> foo curFunc acc varScope) lexScope es

(* don't chain scopes together *)
and fooIter curFunc lexScope varScope es =
  List.iter (fun e -> ignore (foo curFunc lexScope varScope e)) es

let checkVars e =
  let init = List.fold_left
               (fun env x -> IdSet.add x env) IdSet.empty
               ("assert" :: predefinedVars) in
  try ignore (foo "TOP_LEVEL" init IdSet.empty e)
  with NeedVarLifting(foo,x) ->
         Log.printParseErr (spr
           "function [%s] refers to [%s] before declaration\n\n\
            to enable variable lifting: -varLifting true"
              foo x)
     | NeedImplicitGlobal(foo,x) ->
         Log.printParseErr (spr
           "function [%s] refers to [%s] that is not declared\n\n\
            to enable implicit reads/writes to global: -implicitGlobal true"
              foo x)


(***** Label munging **********************************************************)

(* This maps an EJS.expr to a new EJS.expr, doing two things:
   - creating unique ret/break/continue labels
   - recording which break/continue labels are actually jumped to
   - removing all '%' characters are removed from labels inserted by JS->EJS
*)

(* if s is of the form "%blah", return "blah" *)
let trimLabel s =
  if s = "" then ""
  else if s.[0] = '%' then String.sub s 1 (String.length s - 1)
  else s

let mkRetLabel     = let c = ref 0 in fun () -> incr c; spr "return_%d" (!c)
let mkBreakLabel   = let c = ref 0 in fun () -> incr c; spr "break_%d" (!c)
let mkContLabel    = let c = ref 0 in fun () -> incr c; spr "continue_%d" (!c)

let isBreakLabel s = Str.string_match (Str.regexp "^break_.*$") s 0
let isContLabel s  = Str.string_match (Str.regexp "^continue_.*$") s 0

let retStack       = ref ["return_XXXX"]
let breakStack     = ref ["break_XXXX"]
let contStack      = ref ["continue_XXXX"]

let push x stack   = stack := x :: (!stack)
let pop stack      = stack := List.tl (!stack)
let top stack      = List.hd (!stack)

let jumpedTo       = ref StrSet.empty

let rec fooLabelledExpr p x e stack =
  push x stack;
  let e = foo e in
  pop stack;
  E.LabelledExpr (p, x, e)

and foo e = match e with
  | E.VarExpr _ | E.IdExpr _ | E.ConstExpr _ | E.ThisExpr _ -> e
  | E.LabelledExpr (p, x, e) ->
      if x = "%return" then fooLabelledExpr p (mkRetLabel ()) e retStack
      else if x = "%break" then fooLabelledExpr p (mkBreakLabel ()) e breakStack
      else if x = "%continue" then fooLabelledExpr p (mkContLabel ()) e contStack
      else E.LabelledExpr (p, trimLabel x, foo e)
  | E.BreakExpr (p, x, e) -> begin
      let x =
        if x = "%return" then top retStack
        else if x = "%break" then top breakStack
        else if x = "%continue" then top contStack
        else trimLabel x in
      jumpedTo := StrSet.add x !jumpedTo;
      E.BreakExpr (p, x, foo e)
    end
  | E.ArrayExpr (p, es) -> E.ArrayExpr (p, List.map foo es)
  | E.ObjectExpr (p, ps) ->
      E.ObjectExpr (p, List.map (fun (p,f,e) -> (p, f, foo e)) ps)
  | E.NewExpr (p, e, es) -> E.NewExpr (p, foo e, List.map foo es)
  | E.PrefixExpr (p, x, e) -> E.PrefixExpr (p, x, foo e)
  | E.ThrowExpr (p, e) -> E.ThrowExpr (p, foo e)
  | E.HintExpr (p, s, e) -> E.HintExpr (p, s, foo e)
  | E.BracketExpr (p, e1, e2) -> E.BracketExpr (p, foo e1, foo e2)
  | E.InfixExpr (p, x, e1, e2) -> E.InfixExpr (p, x, foo e1, foo e2)
  | E.ForInExpr (p, x, e1, e2) -> E.ForInExpr (p, x, foo e1, foo e2)
  | E.WhileExpr (p, e1, e2) -> E.WhileExpr (p, foo e1, foo e2)
  | E.DoWhileExpr (p, e1, e2) -> E.DoWhileExpr (p, foo e1, foo e2)
  | E.IfExpr (p, e1, e2, e3) -> E.IfExpr (p, foo e1, foo e2, foo e3)
  | E.AssignExpr (p, l, e) -> E.AssignExpr (p, fooLv l, foo e)
  | E.FuncExpr (p, l, e) -> E.FuncExpr (p, l, foo e)
  | E.AppExpr (p, e, es) -> E.AppExpr (p, foo e, List.map foo es)
  | E.LetExpr (p, x, e1, e2) -> E.LetExpr (p, x, foo e1, foo e2)
  | E.SeqExpr (p, e1, e2) -> E.SeqExpr (p, foo e1, foo e2)
  | E.VarDeclExpr (p, x, e) -> E.VarDeclExpr (p, x, foo e)
  | E.TryCatchExpr (p, e1, x, e2) -> E.TryCatchExpr (p, foo e1, x, foo e2)
  | E.TryFinallyExpr (p, e1, e2) -> E.TryFinallyExpr (p, foo e1, foo e2)
  | E.FuncStmtExpr(p,x,l,e) -> E.FuncStmtExpr (p, x, l, foo e)

and fooLv = function
  | E.VarLValue (p, x) -> E.VarLValue (p, x)
  | E.PropLValue (p, e1, e2) -> E.PropLValue (p, foo e1, foo e2)

let freshenLabels e = foo e


(***** Desugaring variables ***************************************************)

(* LamJS desugaring creates a local variable "x" for JS formal "x",
   set to the initial value passed in. so that i can still use the JS
   formals inside types, i'm using a different name for the corresponding
   local variable. *)
let dsVar x = spr "__%s" x

let undoDsVar x = String.sub x 2 (String.length x - 2)


(***** DJS macros *************************************************************)

let oc_macros = open_out (Settings.out_dir ^ "macros.txt")
let debugMacros = true

let macroTable = Hashtbl.create 17
let macroDefs = Hashtbl.create 17

let rec expandMacros s =
  let s' =
    Hashtbl.fold
      (fun x y acc -> Str.global_replace (Str.regexp x) y acc)
      macroTable s 
  in
  if s = s' then s else expandMacros s'

let expandMacros s =
  let s' = expandMacros s in
  if debugMacros && s <> s'
  then fpr oc_macros "%s\n%s\n--->\n%s\n\n" (String.make 80 '-') s s'
  else ();
  s'

let parseMacroDef sOrig =
  let s = Utils.clip sOrig in
  let s = Str.replace_first (Str.regexp "\n") " " s in
  try begin
    if Utils.strPrefix s "#define" then
      let n = String.length "#define " in
      let s = String.sub s n (String.length s - n) in
      let (macro,defn) = Utils.splitAround s ' ' in (* may raise Not_found *)
      let defn = expandMacros defn in (* allow previous macros to be used *)
      let _ = Hashtbl.add macroTable macro defn in
      let _ = Hashtbl.add macroDefs sOrig macro in
      let _ =
        if debugMacros
        then fpr oc_macros "%s\ndef [%s]\n\n%s\n" (String.make 80 '-') macro defn
        else () in
      Some (macro, defn)
    else 
      None
  end with Not_found -> None

let rec collectMacros = function
  (* /*: #define name T */ '#define'; *)
  | E.HintExpr (_, s, E.ConstExpr (_, J.CString "#define"))
  (* '#define name T'; *)
  | E.ConstExpr (_, J.CString(s)) -> ignore (parseMacroDef s)
  | E.SeqExpr (_, e1, e2)         -> (collectMacros e1; collectMacros e2)
  | _                             -> ()


(***** Object.prototype and Array.prototype ***********************************)

let objOp ts ls fn args =
  EApp ((ts,ls,[]), eVar fn, ParseUtils.mkTupleExp args)

(* {Object|Array|Function}.prototype cannot be replaced in DJS, so can
   desugar directly to the following locations and primitives *)

let lObjectPro   = LocConst "lObjPro"
let lArrayPro    = LocConst "lArrPro"
let lFunctionPro = LocConst "lFunPro"

let eObjectPro ()   = eVar "____ObjPro"
let eArrayPro ()    = eVar "____ArrPro"
let eFunctionPro () = eVar "____FunPro"

(*
let eNativePro f l1 l2 =
  objOp [] [LocConst l1; l2] "getPropObj"
    [EDeref (eVar (dsVar f)); EVal (vStr "prototype")]

let eObjectPro ()   = eNativePro "Object" "lObject" lObjectPro
let eArrayPro ()    = eNativePro "Array" "lArray" lObjectPro
let eFunctionPro () = eNativePro "Function" "lFunction" lObjectPro
*)


(***** Parsing DJS annotations ************************************************)

let parseWith production cap s =
  let s = expandMacros s in
  try production LangLexer.token (Lexing.from_string s)
  with Lang.Parse_error(x) ->
         Log.printParseErr
           (spr "couldn't parse annotation as [%s]:\n\n[%s]\n\n%s" cap s x)
     | LangParser2.Error -> (* menhir *)
         Log.printParseErr
           (spr "couldn't parse annotation as [%s]:\n\n[%s]" cap s)

let parseTyp s     = parseWith LangParser2.jsTyp "typ annot" s
let parseAppArgs s = parseWith LangParser2.jsPolyArgs "typ/loc/heap args" s
let parseWhile s   = parseWith LangParser2.jsWhile "while annot" s
let parseHeap s    = parseWith LangParser2.jsHeap "heap annot" s
let parseLoc s     = parseWith LangParser2.jsLoc "loc annot" s
let parseWeakLoc s = parseWith LangParser2.jsWeakLoc "weak loc annot" s
let parseFreeze s  = parseWith LangParser2.jsFreeze "freeze annot" s
let parseThaw s    = parseWith LangParser2.jsThaw "thaw annot" s
let parseCtorTyp s = parseWith LangParser2.jsCtor "ctor annot" s
let parseNew s     = parseWith LangParser2.jsNew "new annot" s
let parseArrLit s  = parseWith LangParser2.jsArrLit "array literal annot" s
let parseMacro s   = parseWith LangParser2.jsMacroDef "macro def" s
let parseObjLocs s =
  match parseWith LangParser2.jsObjLocs "obj loc annot" s with
    | l1, Some(l2) -> (l1, l2)
    | l1, None     -> (l1, lObjectPro)

let maybeParseWith production s =
  let s = expandMacros s in
  try Some (production LangLexer.token (Lexing.from_string s))
  with Lang.Parse_error _ | LangParser2.Error -> None

let maybeParseTcFail s  = maybeParseWith LangParser2.jsFail s


(***** Desugaring environments ************************************************)

(* TODO restore from DjsDesugar.ml *)

type env = { flags: bool IdMap.t; (* types: jstyp IdMap.t *) funcNum: int }

let emptyEnv = {
  funcNum = 0;
  flags = List.fold_left
            (fun acc x -> IdMap.add x false acc)
            IdMap.empty predefinedVars;
  (* types = IdMap.empty *)
}

let addFlag x b env = { env with flags = IdMap.add x b env.flags }

let addVarType env x e =
  env

let updateVarType env x l =
  env

let addFormals t env =
  env

let weakLocs = ref []

let augmentType t env freeVars =
  t

let addCtorType foo tyCtor env =
  env


(***** Typed DS - Free Vars ***************************************************)

(* TODO restore from DjsDesugar.ml *)

let fvExps cap env exprs =
  IdSet.empty


(***** Typed DS - Frame Inf ***************************************************)

(* TODO restore from DjsDesugar.ml *)

let dummyFrame = ParseUtils.typToFrame tyAny

let augmentFrame frame env freeVars =
  frame


(***** Desugaring types *******************************************************)

let oc_desugar_hint = open_out (Settings.out_dir ^ "desugar_hint.txt")

let maybeAddDummyThis = function
  | ((ts,ls,hs),x,TQuick("v",QTuple(tup,b),p),h1,t2,h2)
    when List.length tup = 0 || fst (List.nth tup 0) <> Some("this") ->
      let t1 = TQuick ("v", QTuple ((Some "this", tyAny) :: tup, b), p) in
      ((ts,ls,hs),x,t1,h1,t2,h2)
  | arr ->
      arr


let dsArrow arr =
  arr |> maybeAddDummyThis
      (* |> ParseUtils.maybeAddHeapPrefixVar (* this is called by LangParser2 *) *)

let dsTT = function
  | UArrow(arr) -> UArrow (dsArrow arr)
  | u           -> u

(* TODO remove env if not needed *)
let dsTyp t env =
  mapTyp ~fTT:dsTT t

let desugarTypHint hint env =
  (* let err x = printParseErr (spr "desugarScm\n\n%s\n\n%s" cap x) in *)
  match maybeParseTcFail hint with
    | Some(s) -> Log.printParseErr "TODO DJS failure annotations not implemented"
    | None -> begin
        fpr oc_desugar_hint "%s\n" (String.make 80 '-');
        fpr oc_desugar_hint "hint: [%s]\n\n" hint;
        let t = parseTyp hint in
        let t' = dsTyp t env in
        if t <> t' then fpr oc_desugar_hint "%s\n\n" (strTyp t');
        t'
      end

(* for now, not doing anything different than with any function types *)
let desugarCtorHint hint env =
  dsTyp (tyTypTerm (parseCtorTyp hint)) env

let dsMacro = function
  | MacroT(t) -> MacroT (mapTyp ~fTT:dsTT t)
  | MacroTT(tt) ->
      (match mapTyp ~fTT:dsTT (TQuick("v",QBoxes[tt],pTru)) with
         | TQuick("v",QBoxes[tt'],_) -> MacroTT tt'
         | _                         -> failwith "dsMacro: impossible")


(***** Misc *******************************************************************)

let convertConst = function
  | J.CString(s) -> EVal (wrapVal pos0 (VBase (Str s)))
  | J.CInt(i)    -> EVal (wrapVal pos0 (VBase (Int i)))
  | J.CBool(b)   -> EVal (wrapVal pos0 (VBase (Bool b)))
  | J.CNull      -> EVal (wrapVal pos0 (VNull))
  | J.CUndefined -> EVal (wrapVal pos0 (VBase Undef))
  | J.CNum(f)    -> eVar (spr "_skolem_%d" (Utils.IdTable.process idSkolems f))
  | J.CRegexp _  -> failwith "convert CRegexp"

let eLambda xs e =
  let pat = PNode (List.map (fun x -> PLeaf x) xs) in
  ParseUtils.mkPatFun pat e

let rec eSeq = function
  | []    -> failwith "eSeq: must call with at least one exp"
  | [e]   -> e
  | e::es -> ELet (freshVar "seq", None, e, eSeq es)


(***** Desugaring calls *******************************************************)

let mkApp ?(curried=false) f args =
  if curried then LangUtils.mkApp (eVar f) args
  else begin match args with
    | [x] -> EApp (([],[],[]), eVar f, x)
    | _   -> EApp (([],[],[]), eVar f, (ParseUtils.mkTupleExp args))
  end

let mkCall ts ls func recvOpt args =
  let recv = match recvOpt with Some(e) -> [e] | None -> [EVal vNull] in
  EApp ((ts, ls, []), func, ParseUtils.mkTupleExp (recv @ args))


(***** Desugaring expressions *************************************************)

let funcCount = ref 0

let mkThis i = spr "this%02d" i

let annotateExp ?(lbl="djsAnnotate") e f =
  (* EAs (e, f) *)
  let x = freshVar lbl in ELet (x, Some f, e, eVar x)

let rec ds (env:env) = function

  | E.HintExpr (_, s, E.ConstExpr (_, J.CString "#define")) ->
      if Hashtbl.mem macroDefs s
      then eStr (spr "__ macro %s __" (Hashtbl.find macroDefs s))
      else failwith "ds define: should never happen"

  | E.ConstExpr (_, J.CString(s)) ->
      if Hashtbl.mem macroDefs s
      then eStr (spr "__ macro %s __" (Hashtbl.find macroDefs s))
      else convertConst (J.CString s)

  | E.ConstExpr (_, c) -> convertConst c

  | E.HintExpr (_, h, E.ObjectExpr (p, fields)) ->
      let (l,ci) =
        match maybeParseWith LangParser2.jsLoc h with
          | Some(l) -> (l, None)
          | None    -> (LocConst (freshVar "objLit"), Some (parseTyp h))
      in
      ENewObj (mkEDict env fields, l, eObjectPro (), lObjectPro, ci)

  | E.ObjectExpr (p, fields) ->
      ENewObj (mkEDict env fields, LocConst (freshVar "objLit"),
               eObjectPro (), lObjectPro, None)

  | E.HintExpr (_, h, E.ArrayExpr (_, es)) ->
      (* TODO handle array annotations like objects above *)
      let (l,t) = parseArrLit h in
      ENewObj (mkEArray (Some t) env es, l, eArrayPro (), lArrayPro, None)

  | E.ArrayExpr (_, es) ->
      ENewObj (mkEArray None env es, LocConst (freshVar "arrLit"),
               eArrayPro (), lArrayPro, None)

  | E.ThisExpr p ->
      (* eVar "this" *)                                     (* original LamJS *)
      (* EDeref (eVar (dsVar "this")) *)   (* __this ref cell for thaw/freeze *)
      EDeref (eVar (dsVar (mkThis env.funcNum)))    (* unique "this" per func *)

  | E.IdExpr (p, x) -> ds env (E.VarExpr (p, x))

  | E.VarExpr (p, x) ->
      let _x = dsVar x in
      if not (IdMap.mem x env.flags) then
        Log.printParseErr (spr "bad VarExpr: [%s] undefined" x)
      else if IdMap.find x env.flags then
        EDeref (eVar _x)
      else
        eVar _x

  | E.BracketExpr (_, e1, e2) -> begin
      let ((ts,ls,hs),e1) =
        match e1 with
          | E.HintExpr (_, h, e1) -> (parseAppArgs h, e1)
          | _                     -> (([],[],[]), e1) in
      if hs <> [] then failwith "x[k] shouldn't have heap args";
      match e2 with
        | E.ConstExpr (_, J.CInt i) ->
            objOp ts ls "getIdx" [ds env e1; EVal (vInt i)]
        | E.ConstExpr (_, J.CString s) ->
            objOp ts ls "getProp" [ds env e1; EVal (vStr s)]
        | _ ->
            objOp ts ls "getElem" [ds env e1; ds env e2]
    end

  | E.PrefixExpr (_, "prefix:delete", E.BracketExpr (_, ed, ek)) -> begin
      let ((ts,ls,hs),ed) =
        match ed with
          | E.HintExpr (_, h, ed) -> (parseAppArgs h, ed)
          | _                     -> (([],[],[]), ed) in
      if hs <> [] then failwith "delete x[k] shouldn't have heap args";
      match ek with
        | E.ConstExpr (_, J.CInt i) ->
            objOp ts ls "delIdx" [ds env ed; EVal (vInt i)]
        | E.ConstExpr (_, J.CString s) ->
            objOp ts ls "delPropObj" [ds env ed; EVal (vStr s)]
        | _ ->
            objOp ts ls "delElem" [ds env ed; ds env ek]
    end

  | E.PrefixExpr (_, "prefix:delete", _) ->
      Log.printParseErr "delete not applied to property"

  | E.PrefixExpr (_, op, e) ->
      let e0 =
        match op with
          | "prefix:typeof" -> "js_typeof"
          | "prefix:!"      -> "js_not"
          | "prefix:-"      -> "js_uminus"
          | x               -> failwith (spr "Op1Prefix [%s]" x)
      in
      mkApp e0 [ds env e]

  | E.InfixExpr (_, "in", ek, ed) -> begin
      let ((ts,ls,hs),ed) =
        match ed with
          | E.HintExpr (_, s, ed) -> (parseAppArgs s, ed)
          | _                     -> (([],[],[]), ed) in
      if hs <> [] then failwith "(k in d) shouldn't have heap args";
      match ek with
        | E.ConstExpr (_, J.CInt i) ->
            objOp ts ls "hasIdx" [ds env ed; EVal (vInt i)]
        | E.ConstExpr (_, J.CString s) ->
            objOp ts ls "hasProp" [ds env ed; EVal (vStr s)]
        | _ ->
            objOp ts ls "hasElem" [ds env ed; ds env ek]
    end

  | E.InfixExpr (p, "!=", e1, e2) ->
      mkApp "js_not" [ds env (E.InfixExpr (p, "==", e1, e2))]

  | E.InfixExpr (p, "!==", e1, e2) ->
      mkApp "js_not" [ds env (E.InfixExpr (p, "===", e1, e2))]

  | E.InfixExpr (_, op, e1, e2) ->
      let e0 =
        match op with
          | "+"   -> "js_plus"
          | "-"   -> "js_minus"
          | "*"   -> "js_mult"
          | "/"   -> "js_div"
          | "=="  -> "js_eek"
          | "===" -> "js_threek"
          | ">"   -> "js_gt"
          | ">="  -> "js_ge"
          | "<="  -> "js_le"
          | "<"   -> "js_lt"
          | "&&"  -> "js_and"
          | "||"  -> "js_or"
          | _     -> failwith (spr "Op2Infix [%s]" op)
      in
      mkApp e0 [ds env e1; ds env e2]

  | E.IfExpr (_, e1, e2, e3) -> 
      EIf (ds env e1, ds env e2, ds env e3)

  | E.HintExpr (_, h, E.ConstExpr (_, J.CString "#freeze")) ->
      let (x,l,thaw) = parseFreeze h in
      let _x = eVar (dsVar x) in
      ESetref (_x, EFreeze (l, thaw, EDeref _x))

  | E.HintExpr (_, h, E.ConstExpr (_, J.CString "#thaw")) ->
      let (x,l) = parseThaw h in
      let _x = eVar (dsVar x) in
      ESetref (_x, EThaw (l, EDeref _x))

  | E.AssignExpr (_, E.VarLValue (_, x), e) -> 
      let _x = dsVar x in
      if IdMap.mem x env.flags
      then ESetref (eVar _x, ds env e)
      else Log.printParseErr (spr "can't assign to undefined var [%s]" x)

  | E.AssignExpr (_, E.PropLValue (_, e1, e2), e3) -> begin
      let ((ts,ls,hs),e1) =
        match e1 with
          | E.HintExpr (_, h, e1) -> (parseAppArgs h, e1)
          | _                     -> (([],[],[]), e1) in
      if hs <> [] then failwith "x[k] = y shouldn't have heap args";
      match e2 with
        | E.ConstExpr (_, J.CInt i) ->
            objOp ts ls "setIdx" [ds env e1; EVal (vInt i); ds env e3]
        | E.ConstExpr (_, J.CString s) ->
            objOp ts ls "setProp" [ds env e1; EVal (vStr s); ds env e3]
        | _ ->
            objOp ts ls "setElem" [ds env e1; ds env e2; ds env e3]
    end

  | E.LetExpr (_, x, e1, e2) ->
      let _x = dsVar x in
      ELet (_x, None, ds env e1, ds (addFlag x false env) e2)

  (* rkc: catching VarDeclExpr within SeqExpr so i can turn it into a
       normal let-binding instead of doing var lifting or implicit
       updates to global *)

  (* var f = function (...) { ... }; e2
     insert the hint "f" so that the type macro f is used *)
  | E.SeqExpr (p0,
        E.VarDeclExpr (p1, x, (E.FuncExpr _ as e1)),
        e2) ->
      let e1 = E.HintExpr (p1, x, e1) in
      ds env (E.SeqExpr (p0, E.VarDeclExpr (p1, x, e1), e2))

  (* x.f = function (...) { ... }; e2
     insert the hint "f" so that the type macro f is used *)
  | E.SeqExpr (p0,
        E.AssignExpr (p1,
          (E.PropLValue (_, _, E.ConstExpr (_, J.CString f)) as eLHS),
          (E.FuncExpr _ as eRHS)),
        e2) ->
      let eRHS = E.HintExpr (p1, f, eRHS) in
      ds env (E.SeqExpr (p0, E.AssignExpr (p1, eLHS, eRHS), e2))

  (* function f(...) { ... }; e2
     insert the hint "new f" so that the type macro f is used *)
  | E.SeqExpr (p0, (E.FuncStmtExpr (p1, f, _, _) as e1), e2) ->
      let e1 = E.HintExpr (p1, spr "new %s" f, e1) in
      ds env (E.SeqExpr (p0, e1, e2))

  (* var x /*: T */ = e1; e2
     i added this case to the JS LangParser2 and JS-to-EJS conversion *)
  | E.SeqExpr (_, E.HintExpr (_, s, E.VarDeclExpr (_, x, e1)), e2) ->
      let t = desugarTypHint s env in
      dsVarDecl ~locInvariant:(Some(t)) env x e1 e2

  (* var x = /*: T */ "#extern"; e2 *)
  | E.SeqExpr (_,
      E.VarDeclExpr (_, x,
        E.HintExpr (_, s, E.ConstExpr (_, J.CString "#extern"))), e2) ->
      let _x = dsVar x in
      EExtern (_x, desugarTypHint s env, ds (addFlag x false env) e2)

  (* rkc: 3/15 match this case if i wanted to look for recursive functions as
         var fact = function f(n) /*: ... */ {};
  | E.SeqExpr (_,
      E.VarDeclExpr (_, x, E.HintExpr (_, s, E.FuncStmtExpr (p, f, args, body))), e2) ->
      printParseErr "good"
  *)

  (* var x = e1; e2 *)
  | E.SeqExpr (_, E.VarDeclExpr (_, x, e1), e2) ->
      dsVarDecl env x e1 e2

  | E.VarDeclExpr _ ->
      Log.printParseErr "ds VarDeclExpr: shouldn't get here"

  | E.SeqExpr (_, E.HintExpr (_, s, E.ConstExpr (_, J.CString "#weak")), e2) ->
      let (m,t,l) = parseWeakLoc s in
      (* TODO store weak locs differently in env *)
      let _ = weakLocs := (m,l) :: !weakLocs in
      EWeak ((m, dsTyp t env, l), ds env e2)

  | E.SeqExpr (_, E.HintExpr (_, s, E.ConstExpr (_, J.CString "#type")), e2) ->
      let (x,m) = parseMacro (spr "type %s" s) in
      let m = dsMacro m in
      EMacro (x, m, ds env e2)

  | E.SeqExpr (_, E.HintExpr (_, s, E.FuncStmtExpr (p, f, args, body)), e2) ->
      let _f = dsVar f in
      let t = desugarCtorHint s env in
      let env = addFormals t env in

      (* 4/9: unfortunate that have to call addFlag here, since dsFunc does
         it too *)
      let env = List.fold_left (fun env arg -> addFlag arg true env) env args in
      let t = augmentType t env (fvExps "dsFuncStmtExpr recursive" env [body]) in

      let ctorFun =
        annotateExp ~lbl:"djsCtorType"
          (dsFunc(*true*)env args body) (ParseUtils.typToFrame t) in
      let protoObj =
        ENewObj (EDict [],
                 LocConst (spr "l%sProto" f),
                 eObjectPro (), lObjectPro, None) in
      let ctorObj = 
        ENewObj (EDict [(eStr "code", ctorFun); (eStr "prototype", protoObj)],
                 LocConst (spr "l%sObj" f),
                 eFunctionPro (), lFunctionPro, None) in
      let env = addFlag f true env in
      let env = addCtorType f t env in
      ELet (_f, None, ENewref (LocConst (spr "&%s" f), ctorObj, None),
            ds env e2)

  | E.SeqExpr (_, e1, e2) -> 
      eSeq [ds env e1; ds env e2]

  | E.HintExpr (_, s, E.LabelledExpr (_, bl, E.WhileExpr (_, test, e2)))
      when isBreakLabel bl ->
    begin
      match e2 with
        | E.LabelledExpr(_,cl,body) when isContLabel cl ->
            dsWhile env bl cl test body (parseWhile s)
        | E.SeqExpr(_,E.LabelledExpr(_,cl,body),incr) when isContLabel cl ->
            dsFor env bl cl test body incr (parseWhile s)
        | _ ->
            Log.printParseErr "desugar EJS while fail"
    end

  | E.HintExpr (_, s, E.LabelledExpr (_, bl, E.DoWhileExpr (_, e1, test)))
      when isBreakLabel bl ->
    begin
      match e1 with
        | E.LabelledExpr(_,cl,body) when isContLabel cl ->
            dsDoWhile env bl cl test body (parseWhile s)
        | _ ->
            Log.printParseErr "desugar annotated do/while fail"
    end

  | E.LabelledExpr (_, bl, E.WhileExpr (_, test, e2)) when isBreakLabel bl ->
(*
      if !Settings.augmentHeaps then begin
*)
      if true then begin
        match e2 with
          | E.LabelledExpr(_,cl,body) when isContLabel cl ->
              dsWhile env bl cl test body dummyFrame
          | E.SeqExpr(_,E.LabelledExpr(_,cl,body),incr) when isContLabel cl ->
              dsFor env bl cl test body incr dummyFrame
          | _ ->
              Log.printParseErr "desugar EJS unannotated while fail"
      end else
        failwith "djsDesugar: unannotated while or for"

  | E.LabelledExpr (_, bl, E.DoWhileExpr (_, e1, test)) when isBreakLabel bl ->
    begin
      failwith "djsDesugar: unannotated dowhile"
    end

  | E.WhileExpr _
  | E.DoWhileExpr _ ->
      Log.printParseErr "EJS always wraps while and do/while with %break label"

  | E.HintExpr (_, s, E.SeqExpr (_,
      init_e,
      E.LabelledExpr (_, bl, E.SeqExpr (_,
        E.ForInExpr (_, k, obj, E.LabelledExpr (_, cl, body)),
        E.ConstExpr (_, J.CUndefined)))))
          when isBreakLabel bl && isContLabel cl ->
      if StrSet.mem cl !jumpedTo then failwith "forin has continue"
      else eSeq [ds env init_e; dsForIn env bl k obj body (parseWhile s)]

  | E.ForInExpr (p, x, obj, body) -> failwith "forin"

  | E.LabelledExpr (_, l, e) -> ELabel (trimLabel l, ds env e)

  | E.BreakExpr (_, l, e) -> EBreak (trimLabel l, ds env e)

  | E.AppExpr (_, E.VarExpr (_, "assert"), es) -> begin
      match es with
        | [E.HintExpr (_, s, e)] -> dsAssert env s e
        | [e]                    -> dsAssert env "{(= v true)}" e
        | _                      -> Log.printParseErr "bad assert syntax"
    end

  | E.AppExpr (p,
        E.BracketExpr (_, f, E.ConstExpr (_, J.CString "apply")), obj::args) ->
      mkCall [] [] (ds env f) (Some (ds env obj)) (List.map (ds env) args)

  | E.AppExpr (p, E.HintExpr (_, s, E.BracketExpr (p', obj, prop)), args) ->
    begin
      let (ts,ls,hs) = parseAppArgs s in
      if hs <> [] then failwith "x[k] shouldn't have heap args";
      dsMethCall env ts ls obj prop args 
    end

  | E.AppExpr (p, E.BracketExpr (p', obj, prop), args) ->
      dsMethCall env [] [] obj prop args 

  | E.AppExpr (p, f, args) ->
      let (f,(ts,ls,hs)) =
        match f with
          | E.HintExpr(_,h,f) -> (f, parseAppArgs h)
          | _                 -> (f, ([],[],[])) in
      let _ = if hs <> [] then Log.printParseErr "why passing heap args" in
      mkCall ts ls (ds env f) None (List.map (ds env) args)

  | E.NewExpr (_, E.HintExpr (_, s, constr), args) -> begin

      (* providing at least the lFunctionProto loc param, the other will
         be inferred *)
      let funcObj = ds env constr in
      let ctor =
        objOp [] [lFunctionPro] "getPropObj" [funcObj; eStr "code"] in
      (* 4/11 *)
      let ctor =
        if !Settings.assistCtor then failwith "restore from DjsDesugar.ml ctor"
        else ctor in
      let proto =
        objOp [] [lFunctionPro] "getPropObj" [funcObj; eStr "prototype"] in

      let ((ts,ls,hs),lProto) = parseNew s in
      let lObj =
        match ls with
          | lObj::_ -> lObj
          | _ -> Log.printParseErr "new annot: must have at least 1 loc arg"
      in
      let obj =
        ENewObj (EVal (wrapVal pos0 VEmpty), lObj, proto, lProto, None) in
      mkCall ts ls ctor (Some obj) (List.map (ds env) args)
    end

  | E.NewExpr _ -> Log.printParseErr "new must have annotations"

  | E.FuncExpr (_, args, _) ->
      Log.printParseErr (spr
        "function expression with formals [%s] not annotated"
           (String.concat ", " args))

  (* TODO test recursion *)
  | E.HintExpr (_, s, E.FuncStmtExpr (p, f, args, body)) ->
      let t = desugarTypHint s env in
(*
      let _f = dsVar f in
*)
      let env = addFlag f false env in
      let env = addFormals t env in
      (* 4/9: unfortunate that have to call addFlag here, since dsFunc does
         it too
      *)
      let env = List.fold_left (fun env arg -> addFlag arg true env) env args in
      (* let env = if hasThisParam t then addFlag "this" true env else env in *)
      let env = addFlag "this" true env in
      let t = augmentType t env (fvExps "dsFuncStmtExpr recursive" env [body]) in
      (* let func = dsFunc (hasThisParam t) env p args body in *)
      let func = dsFunc env args body in
      EApp (([t],[],[]), eVar "fix", EFun (PLeaf f, func))

  | E.FuncStmtExpr (_, f, _, _) ->
      Log.printParseErr (spr "function statement [%s] not annotated" f)

  | E.HintExpr (_, s, E.FuncExpr (_, args, body)) ->
      dsAnnotatedFuncExpr env s args body

  | E.HintExpr (_, s, _) ->
      Log.printParseErr
        (spr "use assert(...) rather than general annotation\n\n[%s]" s)

  | E.ThrowExpr _ -> failwith "throwexpr"
  | E.TryFinallyExpr _ -> failwith "try finally"
  | E.TryCatchExpr _ -> failwith "try catch"

and mkEDict env fields =
  EDict (List.map (fun (_, f, e) -> (eStr f, ds env e)) (dsFields fields))

and mkEArray topt env es =
  let t = match topt with Some(t) -> t | None -> tyArrDefault in
  EArray (t, List.map (ds env) es)

and dsFields fields =
  List.map (fun (p,f,e) ->
    match e with
      (* { f: function (...) { ... }, ...}
         insert the hint "f" so that the type macro f is used *)
      | E.FuncExpr _ -> (p, f, E.HintExpr (p, f, e))
      | _            -> (p, f, e)) fields

and dsAnnotatedFuncExpr env s args body =
  let t = desugarTypHint s env in
  let env = addFormals t env in
  let env = List.fold_left (fun env arg -> addFlag arg true env) env args in
  let t = augmentType t env (fvExps "dsAnnotatedFuncExpr" env [body]) in
  (* let e = dsFunc (hasThisParam t) env p args body in *)
  let e = dsFunc env args body in
  annotateExp ~lbl:"djsFuncType" e (ParseUtils.typToFrame t)

and dsAssert ?(lbl="djsAssert") env s = function
  | E.FuncExpr _ -> Log.printParseErr "don't put lambda inside assert(...)"
  | e -> let f = ParseUtils.typToFrame (desugarTypHint s env) in
         annotateExp ~lbl (ds env e) f

and dsMethCall env ts ls obj prop args =
  let obj = ds env obj in
  let func =
    match prop with
      | E.ConstExpr (_, J.CString s) ->
          objOp ts ls "getProp" [obj; EVal (vStr s)]
      | _ ->
          objOp ts ls "getElem" [obj; ds env prop]
  in
 (* TODO for now, just passing the same poly args, but this probably
    will not work in general *)
  mkCall ts ls func (Some obj) (List.map (ds env) args)

(* this version does not use an "arguments" array *)
and dsFunc env args body =
  (* generate a fresh "this" and store it in env *)
  let thisi = incr funcCount; mkThis !funcCount in
  let args = thisi :: args in
  let env = { env with funcNum = !funcCount } in
  let env = List.fold_left (fun env x -> addFlag x true env) env args in
  let body =
    List.fold_left (fun acc x ->
      let _x = dsVar x in
      ELet (_x, None, ENewref (LocConst (spr "&%s" x), eVar x, None), acc)
    ) (ds env body) (List.rev args) in
  eLambda args body

(* rkc: based on LamJS E.WhileExpr case *)
and dsWhile env breakL continueL test body frame =
  let free = fvExps "dsWhile" emptyEnv [test;body] in (* notice emptyEnv *)
  let frame = augmentFrame frame env free in
  let (hs,e1,(t2,e2)) = frame in
  let f = freshVar "while" in
  let loop () = mkApp f [EVal vUndef] in
  let u = (([],[],hs), freshVar "dummy", tyAny, e1, t2, e2) in
  let body =
    if StrSet.mem continueL !jumpedTo
    then Log.printParseErr "dsWhile continue"
         (* ELabel (continueL, Some (AFrame (h1, (STyp tyAny, h1))), ds env body) *)
    else ds env body in
  let fixloop =
    ParseUtils.mkLetRec f u
      (EIf (ds env test, eSeq [body; loop ()], EVal vUndef))
      (loop ()) in
  if StrSet.mem breakL !jumpedTo
  (*
  then ELabel (breakL, Some frame, fixloop)
  *)
  then failwith "use world and label"
  else fixloop

(* rkc: based on LamJS E.DoWhileExpr case *)
and dsDoWhile env breakL continueL test body frame =
  let free = fvExps "dsDoWhile" emptyEnv [test;body] in (* notice emptyEnv *)
  let frame = augmentFrame frame env free in
  let (hs,e1,(t2,e2)) = frame in
  let f = freshVar "dowhile" in
  let loop () = mkApp f [EVal vUndef] in
  let u = (([],[],hs), freshVar "dummy", tyAny, e1, t2, e2) in
  let body =
    if StrSet.mem continueL !jumpedTo
    then Log.printParseErr "dsDoWhile continue"
         (* ELabel (continueL, Some (AFrame (h1, (STyp tyAny, h1))), ds env body) *)
    else ds env body in
  let fixloop =
    ParseUtils.mkLetRec f u
      (eSeq [body; EIf (ds env test, loop (), EVal vUndef)])
      (loop ()) in
  if StrSet.mem breakL !jumpedTo
  (*
  then ELabel (breakL, Some frame, fixloop)
  *)
  then failwith "use world and label"
  else fixloop

(* rkc: based on EJS case for J.ForStmt
     note that by this time, the init statement has been de-coupled from
     the rest of the for statement. see notes on desugaring.
*)
and dsFor env breakL continueL test body incr frame =
  let free = fvExps "dsFor" emptyEnv [test;body;incr] in (* notice emptyEnv *)
  let frame = augmentFrame frame env free in
  let (hs,e1,(t2,e2)) = frame in
  let f = freshVar "forwhile" in
  let loop () = mkApp f [EVal vUndef] in
  let u = (([],[],hs), freshVar "dummy", tyAny, e1, t2, e2) in
  let body =
    if StrSet.mem continueL !jumpedTo
    then failwith "dsFor continue"
         (* ELabel (continueL, Some (AFrame (h1, (STyp tyAny, h1))), ds env body) *)
    else ds env body in
  let fixloop =
    ParseUtils.mkLetRec f u
      (EIf (ds env test,
            eSeq [body; ds env incr; loop ()],
            EVal vUndef))
      (loop ()) in
  if StrSet.mem breakL !jumpedTo
  (*
  then ELabel (breakL, Some frame, fixloop)
  *)
  then failwith "use world and label"
  else fixloop

and dsForIn env breakL k obj body frame =
  let (hs,e1,(t2,e2)) = frame in
  let f = freshVar "forin" in
  let ek = eVar (dsVar k) in
  let writeStr () = ESetref (ek, mkApp "randStr" [eStr "unitval"]) in
  let loop () = mkApp f [eStr "unitval"] in
  let u = (([],[],hs), freshVar "dummy", tyAny, e1, t2, e2) in
  let body = ds env body in
  let fixloop =
    ParseUtils.mkLetRec f u
      (EIf (objOp [] [] "hasElem" [ds env obj; EDeref ek],
            eSeq [body; writeStr (); loop ()],
            EVal vUndef))
      (eSeq [writeStr (); loop ()]) in
  if StrSet.mem breakL !jumpedTo
  (*
  then ELabel (breakL, Some frame, fixloop)
  *)
  then failwith "use world and label"
  else fixloop

(* rkc: creates a traditional lexically-scoped let-binding to a reference *)
and dsVarDecl ?(lxo=None) ?(locInvariant=None) env x e e2 =
  let _x = dsVar x in
  let e = ds env e in
  let env = addVarType env x e in
  let lx = match lxo with Some(l) -> l | None -> LocConst (spr "&%s" x) in
  ELet (_x, None, ENewref (lx, e, locInvariant), ds (addFlag x true env) e2)

let desugar e =
  checkVars e;
  let e = freshenLabels e in
  collectMacros e;
  ds emptyEnv e


(***** Sequencing EJS expressions *********************************************)

(* The JS LangParser2 doesn't have a "prelude" production, so this fakes it by
   stitching together e1 and e2 as if e1 were a prelude. Assumes that e1 is
   a sequence terminated by undefined. This is better than SeqExpr(e1,e2),
   which is no longer a flat top-level sequence. *)

let makeFlatSeq e1 e2 =
  let rec foo = function
    | E.SeqExpr (p, e, E.ConstExpr (_, J.CUndefined)) -> E.SeqExpr (p, e, e2)
    | E.SeqExpr (p, e1, e2) -> E.SeqExpr (p, e1, foo e2)
    | _ -> failwith "makeFlatSeq"
  in
  foo e1

