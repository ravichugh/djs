
open Lang
open LangUtils

module E = Exprjs_syntax
module J = JavaScript_syntax
module L = Lambdajs_syntax

module IdMap = Prelude.IdMap
module IdSet = Prelude.IdSet
module IdSetExt = Prelude.IdSetExt

module StrSet = Utils.StrSet


(***** Check variable scopes **************************************************)

exception NeedVarLifting of Prelude.id * Prelude.id
exception NeedImplicitGlobal of Prelude.id * Prelude.id

let rec foo curFunc lexScope varScope = function
  | E.VarExpr (_, x) ->
      if        not (IdSet.mem x lexScope) &&
                IdSet.mem x varScope &&
                not (!Settings.doVarLifting) then
                  raise (NeedVarLifting (curFunc, x))
      else if   not (IdSet.mem x lexScope) &&
                not (IdSet.mem x varScope) &&
                not (!Settings.doImplicitGlobal) then
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
  let init = IdSet.add "assert" IdSet.empty in
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


(***** Parsing DJS annotations ************************************************)

let parseWith production cap s =
  let s = expandMacros s in
  try production LangLexer.token (Lexing.from_string s)
  with Lang.Parse_error(x) ->
         Log.printParseErr
           (spr "couldn't parse annotation as [%s]:\n\n[%s]\n\n%s" cap s x)
     | LangParser.Error -> (* menhir *)
         Log.printParseErr
           (spr "couldn't parse annotation as [%s]:\n\n[%s]" cap s)

let parseTyp s     = parseWith LangParser.jsTyp "typ annot" s
let parseAppArgs s = parseWith LangParser.jsPolyArgs "typ/loc/heap args" s
let parseWhile s   = parseWith LangParser.jsWhile "while annot" s
let parseHeap s    = parseWith LangParser.jsHeap "heap annot" s
let parseLoc s     = parseWith LangParser.jsLoc "loc annot" s
let parseWeakLoc s = parseWith LangParser.jsWeakLoc "weak loc annot" s
let parseFreeze s  = parseWith LangParser.jsFreeze "freeze annot" s
let parseThaw s    = parseWith LangParser.jsThaw "thaw annot" s
(*
let parseWeakLoc s =
  let l = parseLoc s in
  if isWeakLoc l then l
  else printParseErr (spr "[%s] isn't a weak loc" (strLoc l))
*)
let parseCtorTyp s = parseWith LangParser.jsCtor "ctor annot" s
let parseNew s     = parseWith LangParser.jsNew "new annot" s
let parseArrLit s  = parseWith LangParser.jsArrLit "array literal annot" s
let parseObjLocs s =
  match parseWith LangParser.jsObjLocs "obj loc annot" s with
    | l1, Some(l2) -> (l1, l2)
    | l1, None     -> (l1, lObjectPro)

let maybeParseWith production s =
  let s = expandMacros s in
  try Some (production LangLexer.token (Lexing.from_string s))
  with Lang.Parse_error _ | LangParser.Error -> None

let maybeParseTcFail s  = maybeParseWith LangParser.jsFail s


(***** Desugaring variables ***************************************************)

(* normal desugaring creates a local variable "x" for JS formal "x",
   set to the initial value passed in. so that i can still use the JS
   formals inside types, using a different name for the corresponding
   local variable. *)
let dsVar x = spr "__%s" x

let undoDsVar x = String.sub x 2 (String.length x - 2)


(***** Object.prototype and Array.prototype ***********************************)

let objOp ts ls fn args =
  let fn = if !Settings.fullObjects then fn else fn ^ "Lite" in
  EApp ((ts,ls,[]), eVar fn, ParseUtils.mkTupleExp args)

(* by using these locations when desugaring object literals, array literals,
   and constructor functions, i'm optimistically assuming that
   {Object|Array|Function}.prototype have not been replaced.
   that is, Object.prototype is still Ref(lObjectProto). *)
let lObjectPro   = lObjectPro (* defined in lang.ml *)
let lArrayPro    = LocConst "lArrayProto"
let lFunctionPro = LocConst "lFunctionProto"

(*
let eNativePro f l1 l2 =
  objOp [] [LocConst l1; l2] "getPropObj"
    [EDeref (eVar (dsVar f)); EVal (vStr "prototype")]

let eObjectPro ()   = eNativePro "Object" "lObject" lObjectPro
let eArrayPro ()    = eNativePro "Array" "lArray" lObjectPro
let eFunctionPro () = eNativePro "Function" "lFunction" lObjectPro
*)

(* assuming {Object|Array|Function}.prototype haven't been overwritten
   to make things a bit faster. *)
let eObjectPro ()   = eVar (dsVar "__ObjectProto")
let eArrayPro ()    = EDeref (eVar (dsVar "__ArrayProto"))
let eFunctionPro () = EDeref (eVar (dsVar "__FunctionProto"))


(***** Desugaring environments ************************************************)

(* 3/31 *)

(* 4/3 *)

type jsarrlen = int option option

let pArrLen = function
  | Some(Some i) -> pAnd [packed theV; eq (arrlen theV) (wInt i)]
  | Some(None)   -> packed theV
  | None         -> PTru

let strArrLen = function
  | Some(Some i) -> spr "len %d" i
  | Some(None)   -> "packed"
  | None         -> "unbounded"

let strVarOpt = function Some(x) -> x | None -> "_"

type jsrecd = (string * typ) list * bool (* true if domain is exact *)

let strJsRecd (l,b) =
  spr "{%s (%b)}"
    (String.concat "; "
       (List.map (fun (x,t) -> spr "%s:%s" x (prettyStrTyp t)) l)) b

type jstyp =
  | JsObject of loc * loc * jsrecd * vvar option
  | JsArray of typ * loc * loc * jsarrlen * vvar option (* binder from heap *)
  | JsInt of bool (* true if >= 0 *)
  | JsLen of vvar (* length of an array *)
  | JsNum
  | JsStr
  | JsTop
  | JsWeakObj of loc
  | JsAnnotate of typ (* these come from annotations, dsAssert *)
  (* NOTE if i end up dealing with ctor/prototype objects in the
     macro pre-pass, then there's no real benefit to keep JsCtor
     separate for JsObject during desugaring *)
  | JsCtor of vvar * typ * loc * loc
      (* name of constructor,
         type of constructor function,
         location of constructor object (always lFooObj),
         location of ctor object's parent (always lFunctionProto) *)
(*
  | JsProto of vvar * (string * typ) list * loc * loc
      (* name of constructor this "prototype" corresponds to,
         fields it definitely has,
         location (always lFooProto),
         location of its parent (always lObjectProto) *)
*)

let strJsTyp = function
  | JsInt(b) -> if b then "int >= 0" else "int"
  | JsNum -> "num"
  | JsStr -> "str"
  | JsTop -> "top"
  | JsLen(x) -> spr "len(%s)" x
  | JsObject(l1,l2,r,xo) ->
      spr "object %s %s %s %s" (strLoc l1) (strLoc l2)
        (strJsRecd r) (strVarOpt xo)
  | JsArray(t,l1,l2,al,xo) ->
      spr "array %s %s %s %s %s" (prettyStrTyp t) (strLoc l1) (strLoc l2)
        (strArrLen al) (strVarOpt xo)
  | JsWeakObj(l) -> spr "weak object %s" (strLoc l)
  | JsAnnotate(t) -> spr "annotate (...)"
  | JsCtor(f,t,l1,l2) ->
      spr "constructor %s ... ... %s %s" f (strLoc l1) (strLoc l2)
(*
  | JsProto(f,_,l1,l2) ->
      spr "prototype %s ... %s %s" f (strLoc l1) (strLoc l2)
*)

(* using this name to store a binding in the type env for Foo.prototype *)
let myProtoVar f = spr "My%sProto" f

let oc_js_types = open_out (Settings.out_dir ^ "js-types.txt")

let logJsTyp s = fpr oc_js_types "%s\n" s; flush oc_js_types

(* the boolean b in binding (x,b) indicates whether x is a reference.
     if so,  [[ x ]] = deref __x
     if not, [[ x ]] = __x
*)
type env = { flags: bool IdMap.t; types: jstyp IdMap.t }

let addFlag x b env = { env with flags = IdMap.add x b env.flags }
let addType x t env = { env with types = IdMap.add x t env.types }

let emptyEnv = { flags = IdMap.empty; types = IdMap.empty }


(* 4/9: add m |-> frzn to pre and post conditions for all functions *)
let weakLocs = ref []

let locProOfWeak cap m = 
  if List.mem_assoc m !weakLocs then List.assoc m !weakLocs
  else failwith (spr "locProOfWeak: greedy %s" cap)


let rec getType env = function
  | EVal (VBase (Str _)) -> JsStr
  | EVal (VBase (Int i)) -> JsInt (i>=0)
  | EApp (_, EVal (VVar "js_uminus"), EVal (VBase (Int i))) -> JsInt (not(i>=0))
  | EVal (VVar sk) when Utils.strPrefix sk "_skolem_" -> JsNum
  | ELet (_, None, ENewObj (EVal VEmpty, l1, _, l2), _) when l2 = lObjectPro ->
      JsObject (l1, l2, ([],false), None)
  | ENewObj (EArray (t, elts), l1, _, l2) when l2 = lArrayPro ->
      JsArray (t, l1, l2, Some (Some (List.length elts)), None)
  | EVal (VVar x) | EDeref (EVal (VVar x)) ->
      if not (IdMap.mem x env.types) then
        (* Log.printParseErr (spr "DjsDesugar.getType [%s]: var not found" x) *)
        let _ = logJsTyp (spr "getType(%s) = NOT FOUND" x) in
        JsTop
      else
        let t = IdMap.find x env.types in
        let _ = logJsTyp (spr "getType(%s) = %s" x (strJsTyp t)) in
        t
(*
  (* 4/1: optimistically assuming that x is a constructor function and its
     prototype field has not been overwritten. sensitive to
     ParseUtils.mkTupleExp. will be much nicer when i add ETuple.  *)
  | EApp(_, EVal (VVar "getPropObj"),
         EDict([(EVal(VBase(Str"0")),EDeref(EVal(VVar(x))));
                (EVal(VBase(Str"1")),EVal(VBase(Str"prototype")))])) ->
      let t =
        (* not doing these three built ins, because their not modeled
           as constructor functions right now *)
        if x = "__Object" then JsTop
        else if x = "__Array" then JsTop
        else if x = "__Function" then JsTop
        else  JsObject (LocConst (spr "l%sProto" (undoDsVar x)), lObjectPro,
                        ([],false), None) in
      let _ = logJsTyp (spr "getType(%s.prototype) = %s" x (strJsTyp t)) in
      t
*)
  (* 4/3: redoing the above case by calling getType, looking for JsCtor
     instead of arbitrary JsObject, and producing a JsPrototype instead
     of an arbitrary JsObject.  *)
  | EApp(_, EVal (VVar "getPropObj"),
         EDict([(EVal(VBase(Str"0")),obj);
                (EVal(VBase(Str"1")),EVal(VBase(Str"prototype")))])) ->
      begin match getType env obj with
        | JsCtor(f,_,_,_) ->
            (* 4/4 since not correctly threading prototypes through
               macros yet, returning a vanilla object instead of JsProto *)
            JsObject (LocConst (spr "l%sProto" (undoDsVar f)), lObjectPro,
                      ([],false), None)
(*
            let fProto = myProtoVar f in
            if IdMap.mem fProto env.types then
              IdMap.find fProto env.types
            else
              Log.printParseErr (spr "getType(%s).prototype" f)
*)
        | _ ->
            let _ = logJsTyp "getType(???.prototype) = top" in
            JsTop
      end
  (* 4/3: TODO might want to look for getProp and getElem also *)
  | EApp(_, EVal (VVar "getPropArr"),
         EDict([(EVal(VBase(Str"0")),arr);
                (EVal(VBase(Str"1")),EVal(VBase(Str"length")))])) ->
      (match getType env arr with
         | JsArray(_,_,_,Some(Some(i)),_)    -> JsInt (i>=0)
         | JsArray(_,_,_,Some(None),Some(a)) -> JsLen a
         | JsArray(_,_,_,Some(None),None)    -> JsInt false
         | _ -> JsTop)
  (* undoing the ParseUtils.typToFrame that dsAssert inserts *)
  | EAs("DjsDesugar",_,([h],([h'],[]),(t,([h''],[])))) when h = h' && h = h'' ->
      (* 4/9: specially looking for weak obj case *)
      (match t with
         | THasTyp([URef(m)],_) when isWeakLoc m -> JsWeakObj m
         | _ -> JsAnnotate t)
  | _ ->
      JsTop

let addVarType env x e =
  let t = getType env e in
  logJsTyp (spr "addVarType(%s) = %s" x (strJsTyp t));
  addType x t env

(* 4/3 switched from JsObject to JsCtor *)
let addCtorType foo tyCtor env =
  (* let t = JsObject (l1, l2, ([],false), None) in *)
  (* these loc args are the same as from the constructor case *)
  let fooOrig = undoDsVar foo in
(*
  let fooProto = myProtoVar foo in
  let lFooProto = spr "l%sProto" fooOrig in
*)
  let lFooObj = spr "l%sObj" fooOrig in
  let t1 = JsCtor (foo, tyCtor, LocConst lFooObj, lFunctionPro) in
(*
  let t2 = JsProto (foo, [], LocConst lFooProto, lObjectPro) in
  logJsTyp (spr "addCtorType(%s) = %s" foo (strJsTyp t1));
  logJsTyp (spr "addProtoType(%s) = %s" fooProto (strJsTyp t2));
  addType fooProto t2 (addType foo t1 env)
*)
  logJsTyp (spr "addCtorType(%s) = %s" foo (strJsTyp t1));
  addType foo t1 env

(*
(* strongly updating Foo.prototype object *)
let updateProtoType foo newField newFieldType env =
  let fooProto = myProtoVar foo in
  if not (IdMap.mem fooProto env.types) then
    Log.printParseErr (spr "updateProtoType [%s]: proto var not found" foo) 
  else
    match IdMap.find fooProto env.types with
      | JsProto(_,fields,l1,l2) ->
          if List.mem newField (List.map fst fields) then
            Log.printParseErr (spr "updateProtoType [%s]: already has field" foo) 
          else
            let t = JsProto (foo, fields @ [(newField,newFieldType)], l1, l2) in
            let _ = logJsTyp (spr "\nupdateProtoType(%s) = with field %s : %s\n"
               fooProto newField (prettyStrTyp newFieldType)) in
            addType fooProto t env
      | _ ->
          Log.printParseErr (spr "updateProtoType [%s]: should be JsProto" foo) 
*)

(* useful for thaw/freeze *)
let updateVarType env x l =
  let (b,t) =
    if isWeakLoc l then (true, JsWeakObj l) else
    match getType env (EDeref (eVar x)) with
      | JsObject(l1,l2,_,_) -> (true, JsObject (l, l2, ([],false), None))
      (* TODO preserve len or x? *)
      | JsArray(t,_,l2,al,x) -> (true, JsArray (t, l, l2, None, None))
      (* 4/10 *)
      | JsWeakObj(m) -> (true, JsObject (l, locProOfWeak "update" m, ([],false), None))
      | t                 -> (false, t)
  in
  if b then logJsTyp (spr "updateVarType(%s) = %s" x (strJsTyp t));
  addType x t env

(* basically copied from TcDref2 for now *)
let findHeapCell l cs =
  try Some (snd (List.find (fun (l',_) -> l = l') cs))
  with Not_found -> None

(* 4/3 optimistically assuming that all predicates are at the top-level *)
let arrLenFromPred p =
  let isPacked =
    foldForm
      (fun acc -> function PApp("packed",[theV]) -> true | _ -> acc)
      false (TRefinement ("dummy", p)) in
  if isPacked then
    Some (foldForm (* TODO *)
            (fun acc -> function | _ -> acc)
            None (TRefinement ("dummy", p)))
  else
    None

let arrLenFromPreds ps = arrLenFromPred (pAnd ps)

(* 4/3 optimistically assuming that all predicates are at the top-level.
   TODO obviously very dependent on structure of formulas right now. *)
let recdTypFrom t =
  let fields =
    foldForm
      (fun acc -> function
         (* TODO this won't collect any refinements on the base type *)
         | PEq(WApp("tag",[WApp("sel",[WVal(VVar"v");WVal(VBase(Str(f)))])]),
               wTag) ->
             (f, ty (eq (tag theV) wTag)) :: acc
         | PUn(HasTyp(WApp("sel",[WVal(VVar"v");WVal(VBase(Str(f)))]),u)) ->
             (f, THasTyp ([u], PTru)) :: acc
         | _ ->
             acc
      ) [] t in
  let wFields = List.map wStr (List.map fst fields) in
  let dom =
    foldForm
      (fun acc -> function
         | PDomEq(WVal(VVar"v"),ws) ->
             List.sort compare ws = List.sort compare wFields
         | _ -> acc)
      false t in
  (fields, dom)

let addFormals t env =
  match t with (* looking for a single arrow *)
  | THasTyp([UArr(_,_,TTuple(ts),(_,cs),_,_)],_) ->
      List.fold_left (fun env (x,t) ->
(*
        let x = if x = "this" then x else dsVar x in
*)
        let x = dsVar x in
        match t with (* could look for optional strong ref if need be *)
        | THasTyp([URef(l1)],_) ->
          if isWeakLoc l1 then 
            let t = JsWeakObj l1 in
            let _ = logJsTyp (spr "addFormalType(%s) = %s" x (strJsTyp t)) in
            addType x t env
          else
          begin match findHeapCell l1 cs with
            (* 4/3 unfortunately had to split the following two cases because
               p and ps are different types *)
            | Some(HConcObj(a,THasTyp([UArray(t)],p),l2)) ->
                let t = JsArray (t, l1, l2, arrLenFromPred p, Some a) in
                let _ = logJsTyp (spr "addFormalType(%s) = %s" x (strJsTyp t)) in
                addType x t env
            | Some(HConcObj(a,TRefinement("v",PConn("and",
                  PUn(HasTyp(WVal(VVar"v"),UArray(t)))::ps)),l2)) ->
                let t = JsArray (t, l1, l2, arrLenFromPreds ps, Some a) in
                let _ = logJsTyp (spr "addFormalType(%s) = %s" x (strJsTyp t)) in
                addType x t env
            | Some(HConcObj(d,t,l2)) ->
                let t = JsObject (l1, l2, recdTypFrom t, Some d) in
                let _ = logJsTyp (spr "addFormalType(%s) = %s" x (strJsTyp t)) in
                addType x t env
            | Some(HConc _) -> failwith "a"
            | _ -> env
          end
        (* TODO 4/9 adding more cases here besides references *)
        | TBaseUnion(["number"]) ->
            let t = JsNum in
            let _ = logJsTyp (spr "addFormalType(%s) = %s" x (strJsTyp t)) in
            addType x t env
        | _ ->
            env
      ) env ts
  | _ -> env

let tyInt = TInt

let tyPosInt = TBaseRefine ("v", tagNum, pAnd [integer theV; ge theV (wInt 0)])

let tyLenOfArr a =
  TBaseRefine ("v", tagNum, pAnd [integer theV; eq theV (arrlen (wVar a))])

let tyJsRecd (fields,b) =
  let wFields = List.map wStr (List.map fst fields) in
  let dom = if b then PDomEq (theV, wFields) else PHas (theV, wFields) in
  let types = List.map (fun (f,t) -> applyTyp t (sel theV (wStr f))) fields in
  ty (pAnd (pDict :: dom :: types))

let tyProtoDict fields =
  let types = List.map (fun (f,t) -> applyTyp t (sel theV (wStr f))) fields in
  ty (pAnd (pDict :: types))

(* TODO 4/9 *)
let jsTypToTyp = function
  | JsInt(b) -> if b then tyPosInt else tyInt
  | JsLen(x) -> ty (eq theV (arrlen (wVar x)))
  | JsNum -> tyNum
  | JsStr -> tyStr
  | JsTop -> tyAny
  | JsAnnotate(t) -> t
  | JsWeakObj(m) -> THasTyp ([URef m], PTru)
  | JsObject _ -> failwith "jsTypToTyp object"
  | JsArray _ -> failwith "jsTypToTyp array"
  | JsCtor _ -> failwith "jsTypToTyp ctor"


(***** Typed DS - Free Vars ***************************************************)
(* TODO 4/8-4/9. combine this with check vars *)

let rec fvExp env acc = function
  | E.VarExpr (_, x) | E.IdExpr (_, x) ->
      if IdMap.mem x env.flags then acc else IdSet.add x acc
  | E.FuncExpr (_, l, e) ->
      failwith "a"
  | E.FuncStmtExpr (_, f, l, e) ->
      let env = List.fold_left (fun env x -> addFlag x true env) env (f::l) in
      fvExp env acc e
  | E.ConstExpr _ -> acc
(*
  | E.ThisExpr _ -> IdSet.add "this" acc
*)
  | E.ThisExpr p -> fvExp env acc (E.VarExpr (p, "this"))
  | E.ArrayExpr (_, es) -> List.fold_left (fvExp env) acc es
  | E.ObjectExpr (_, ps) ->
      let es = List.map (fun (_,_,e) -> e) ps in
      List.fold_left (fvExp env) acc es
  | E.NewExpr (_, c, args) -> List.fold_left (fvExp env) acc (c::args)
  | E.PrefixExpr (_, _, e) -> fvExp env acc e
  | E.HintExpr (_, _, e) -> fvExp env acc e
  | E.BracketExpr (_, e1, e2)
  | E.InfixExpr (_, _, e1, e2)
  | E.ForInExpr (_, _, e1, e2)
  | E.WhileExpr (_, e1, e2)
  | E.DoWhileExpr (_, e1, e2) -> List.fold_left (fvExp env) acc [e1;e2]
  | E.IfExpr (_, e1, e2, e3) -> List.fold_left (fvExp env) acc [e1;e2;e3]
  | E.AssignExpr (_, l, e) -> fvExp env (fvLv env acc l) e
  | E.AppExpr (_, f, args) -> List.fold_left (fvExp env) acc (f::args)
  | E.LetExpr (_, x, e1, e2) ->
      let acc = fvExp env acc e1 in
      fvExp (addFlag x true env) acc e2
  | E.SeqExpr (_, E.VarDeclExpr (_, x, e), e2) ->
      fvExp (addFlag x true env) (fvExp env acc e) e2
  | E.SeqExpr (_, e1, e2) -> List.fold_left (fvExp env) acc [e1;e2]
  | E.LabelledExpr (_, _, e) -> fvExp env acc e
  | E.BreakExpr (_, _, e) -> fvExp env acc e
  | E.VarDeclExpr (_, x, e) -> fvExp env acc e
(*
  | E.ThrowExpr (_, e)
  | E.TryCatchExpr (_, e1, _, e2) -> (* TODO catch bound identifiers *)
      fvFold env acc [e1;e2]
  | E.TryFinallyExpr (_, e1, e2) ->
      fvFold env acc [e1;e2]
*)

and fvLv env acc = function
  | E.VarLValue (_, x) -> if IdMap.mem x env.flags then acc else IdSet.add x acc
  | E.PropLValue (_, e1, e2) -> List.fold_left (fvExp env) acc [e1;e2]

let fvExps cap env exprs =
  if not !Settings.augmentHeaps then IdSet.empty
  else begin
    let freeVars = List.fold_left (fvExp env) IdSet.empty exprs in
    let s = IdSet.fold (fun x acc -> spr "%s %s" acc x) freeVars "" in
    logJsTyp (spr "\nfreeVars %s {%s }" cap s);
    freeVars
  end

let augmentHeap cs env freeVars =
  let tmp () = freshVar "augheap" in
  let newCs1 =
  IdSet.fold (fun x acc ->
    let lx = LocConst (spr "&%s" x) in

(*
    (* TODO if i switch this to a ref, to facilitate thaw inf, then can
       get rid of this special case *)
    if x = "this" then begin
      if not (IdMap.mem x env.types) then acc
      else (match IdMap.find x env.types with
        (* same as case below, but not an extra level of indirection
           because "this" is not a mutable variable *)
        | JsObject(l1,l2,r,_) ->
            if List.mem_assoc l1 cs then acc
            else (l1, HConcObj (tmp(), tyJsRecd r, l2)) :: acc
        | JsArray _ -> failwith "augmentheap this array"
        | _ -> acc)
    end
*)

    if List.mem_assoc lx cs then acc
    else if IdMap.mem (dsVar x) env.types then
      (match IdMap.find (dsVar x) env.types with
         | JsArray(t,l1,l2,alen,ao) ->
             if List.mem_assoc l1 cs then acc
             else (match ao with
               | None ->
                   (lx, HConc (tmp(), tyRef l1)) ::
                   (l1, HConcObj (tmp(), THasTyp ([UArray t], pArrLen alen), l2)) :: acc
               | Some(a) ->
                   (lx, HConc (tmp(), tyRef l1)) ::
                   (l1, HConcObj (tmp(), ty (eq theV (wVar a)), l2)) :: acc)
         | JsObject(l1,l2,r,_) -> (* not using binder, so fields can be written *)
             if List.mem_assoc l1 cs then
               acc
               (* (lx, HConc (tmp(), tyRef l1)) :: acc *) (* TODO *)
             else
               (lx, HConc (tmp(), tyRef l1)) ::
               (l1, HConcObj (tmp(), tyJsRecd r, l2)) :: acc
         | t ->
             (lx, HConc (tmp(), jsTypToTyp t)) :: acc)
    else
      acc
  ) freeVars []
  in
  if newCs1 <> [] then begin
    logJsTyp "augmentHeap added:";
    List.iter (fun (l,hc) ->
      logJsTyp (spr "  %s |-> %s" (strLoc l) (prettyStr strHeapCell hc))
    ) newCs1;
  end;
  (* TODO for now, implementing "sameType" with fresh binders *)
  let newCs2 =
    List.map (function (l,HConc(_,s))       -> (l, HConc (tmp(), s))
                     | (l,HConcObj(_,s,l')) -> (l, HConcObj (tmp(), s, l'))
                     | (l,HWeakTok(ts))     -> (l, HWeakTok ts)) newCs1 in
  (newCs1, newCs2)

let augmentHeap cs env freeVars =
  let (cs1,cs2) = augmentHeap cs env freeVars in
  List.fold_left (fun (acc1,acc2) (m,_) ->
    if List.mem_assoc m cs then (acc1,acc2)
    else begin
      logJsTyp (spr "  %s |-> %s" (strLoc m) (strThawState Frzn));
      ((m, HWeakTok Frzn) :: acc1, (m, HWeakTok Frzn) :: acc2)
    end
  ) (cs1,cs2) !weakLocs

(* 4/9 looking for a single arrow. if so, then add omitted locations. based
   on envToFrame/threadStuff from last week. *)
let augmentType t env freeVars =
  if not !Settings.augmentHeaps then t else
  match t with
    | THasTyp([UArr(l,x,t1,(h1,cs1),t2,(h2,cs2))],p) ->
        let (newCs1,newCs2) = augmentHeap cs1 env freeVars in
        THasTyp ([UArr (l,x,t1,(h1,cs1@newCs1),t2,(h2,cs2@newCs2))], p)
    | t ->
        failwith (spr "augmentType %s" (prettyStrTyp t))

(*
(* TODO this is what a loop annotation should be *)
type preframe = hvars * heap
*)

let augmentFrame frame env freeVars =
  if not !Settings.augmentHeaps then frame
  else let (hvars,(h1,cs1),(t2,(h2,cs2))) = frame in
       let (newCs1,newCs2) = augmentHeap cs1 env freeVars in
       (hvars, (h1, cs1 @ newCs1), (t2, (h2, cs2 @ newCs2)))

let dummyFrame = ParseUtils.typToFrame tyAny

(*

(***** Typed DS - Frame Inf ***************************************************)

let envToFrame env =
  let cs =
    IdMap.fold (fun x t acc ->
      let tmp () = freshVar "frameinf" in
      if x = "this" then begin
        match t with
          (* same as case below, but not an extra level of indirection
             because "this" is not a mutable variable *)
          | JsObject(l1,l2,r,_) ->
              (l1, HConcObj (tmp(), tyJsRecd r, l2)) :: acc
          | _ -> acc
      end
      (* TODO built ins *)
      else if x = dsVar "Object" then acc 
      else if x = dsVar "Array" then acc 
      else if x = dsVar "Function" then acc 
      else if x = dsVar "__FunctionProto" then acc 
      else if x = dsVar "__ArrayProto" then acc 
      else begin
        let lx = LocConst (spr "&%s" (undoDsVar x)) in
        match t with
          | JsInt(b) -> (lx, HConc (tmp(), if b then tyPosInt else tyInt)) :: acc
          | JsStr -> (lx, HConc (tmp(), tyStr)) :: acc
          | JsNum -> (lx, HConc (tmp(), tyNum)) :: acc
          | JsLen(a) -> (lx, HConc (tmp(), tyLenOfArr a)) :: acc
          | JsArray(t,l1,l2,alen,None) ->
              (lx, HConc (tmp(), tyRef l1)) ::
              (l1, HConcObj (tmp(), THasTyp ([UArray t], pArrLen alen), l2)) :: acc
          (* TODO this assumes that array is unmodified by the loop, so that
             len() can refer to the binder for the formal. instead, should probably
             have length refer to the binder generated by envToFrame ... *)
          | JsArray(t,l1,l2,alen,Some(a)) ->
              (lx, HConc (tmp(), tyRef l1)) ::
              (l1, HConcObj (tmp(), ty (eq theV (wVar a)), l2)) :: acc
(*
          (* TODO probably don't want to selfify *)
          | JsObject(l1,l2,_,Some(d)) ->
              (lx, HConc (tmp(), tyRef l1)) ::
              (l1, HConcObj (tmp(), ty (eq theV (wVar d)), l2)) :: acc
*)
          | JsObject(l1,l2,r,_) ->
              (lx, HConc (tmp(), tyRef l1)) ::
              (l1, HConcObj (tmp(), tyJsRecd r, l2)) :: acc
          | _ -> acc
        end
    ) env.types []
  in
  let h = freshHVar () in
  let f = ([h], ([h],cs), (tyAny,([h],cs))) in (* TODO output cs *)
  logJsTyp (spr "\nenvToFrame(...) = %s\n" (prettyStr strFrame f));
  f
*)

(*
(***** Typed DS - Monotonic Heaps *********************************************)

let threadStuff env (l,xIn,t1,(h1,cs1),t2,(h2,cs2)) =
  Printf.printf "threadStuff called\n";
  let (more1,more2) =
    IdMap.fold (fun x t (acc1,acc2) ->
      let lx = LocConst (spr "&%s" (undoDsVar x)) in
      (* if the location is already mentioned explicitly, don't do anything *)
      if List.mem_assoc lx cs1 then (acc1,acc2)
      (* TODO built ins *)
      else if x = dsVar "Object" then (acc1,acc2) 
      else if x = dsVar "Array" then (acc1,acc2) 
      else if x = dsVar "Function" then (acc1,acc2) 
      else if x = dsVar "__FunctionProto" then (acc1,acc2) 
      else if x = dsVar "__ArrayProto" then (acc1,acc2) 
      else begin
        (* TODO factor with envToFrame *)
        let tmp () = freshVar "frameinf" in
        match t with
          | JsInt(b) ->
              let acc1 = (lx, HConc (tmp(), if b then tyPosInt else tyInt)) :: acc1 in
              let acc2 = (lx, HConc (tmp(), if b then tyPosInt else tyInt)) :: acc2 in
              (acc1,acc2)
(*
          | JsStr -> (lx, HConc (tmp(), tyStr)) :: acc
          | JsNum -> (lx, HConc (tmp(), tyNum)) :: acc
*)
          | JsAnnotate(t) ->
              let acc1 = (lx, HConc (tmp(), t)) :: acc1 in
              let acc2 = (lx, HConc (tmp(), t)) :: acc2 in
              (acc1, acc2)
(*
          | JsCtor(f,_,lFooObj,_) ->
              let acc1 = (lx, HConc (tmp(), tyRef lFooObj)) :: acc1 in
              let acc2 = (lx, HConc (tmp(), tyRef lFooObj)) :: acc2 in
              (acc1, acc2)
*)
(*
          | JsProto(_,fields,lFooProto,lObjP) ->
              if List.mem_assoc lFooProto cs1 then (acc1,acc2)
              else
                (* for prototype object, important that output is exact.
                   can't track domain explicitly, since then won't be
                   able to call it later after extension. *)
                let y = tmp () in
                let acc1 = (lFooProto, HConcObj (y, tyProtoDict fields, lObjP))
                           :: acc1 in
                let acc2 = (lFooProto, HConcObj (tmp(), ty (eq theV (wVar y)), lObjP))
                           :: acc2 in
                (acc1, acc2)
*)
          | _ ->
              (acc1,acc2) (* TODO more cases *)
      end
    ) env.types ([],[])
  in
  (l, xIn, t1, (h1, cs1 @ more1), t2, (h2, cs2 @ more2))

let threadStuff env arr =
  let arr = threadStuff env arr in
  logJsTyp (spr "\nthreadStuff(...) = %s\n" (prettyStrTT (UArr(arr))));
  arr

let threadStuffThrough env = function
  | THasTyp([UArr(arr)],p) -> THasTyp ([UArr (threadStuff env arr)], p)
  | t -> t

(*
let isJsProto = function JsProto _ -> true | _ -> false
*)

*)

(***** Desugaring types *******************************************************)

let oc_desugar_hint = open_out (Settings.out_dir ^ "desugar_hint.txt")

(*
let expandAwayTyp t =
  let x = freshVar "_ugh" in
  TRefinement (x, applyTyp t (wVar x))

let expandAwayHeap (hs,cs) =
  let cs =
    List.map (function
      | (l,HConc(x,s)) -> (l, HConc (x, expandAwayTyp s))
      | (l,HConcObj(x,s,l')) -> (l, HConcObj (x, expandAwayTyp s, l'))
    ) cs
  in
  (hs, cs)

let expandAwayDepTuples (t,h) =
  (expandAwayTyp t, expandAwayHeap h)

let depTupleSubst t w =
  let rec foo acc path = function
    | TTuple(l) -> 
        Utils.fold_left_i (fun acc (x,t) i ->
          let path = sel path (wProj i) in
          let acc = (x, path) :: acc in
          foo acc path t
        ) acc l
    | TNonNull(t) | TMaybeNull(t) -> foo acc path t
    | _ -> acc
  in
  List.rev (foo [] w t)
*)

(* all [typArgs; locArgs, l_this, l_args; heapArgs].
       (Ref(l_this) * Ref(l_args))
     / [inH ++ inC, l_this |-> c_this: TOP, l_args |-> c_args: tIn] 
    -> tRet
     / [outH ++ outC, l_this |-> c_this': TOP]
*)
let dsArrowWithArgsArray arr =

  let arr = ParseUtils.maybeAddHeapPrefixVar arr in
  let ((ts,ls,hs),x,tIn,(inH,inC),tRet,(outH,outC)) = arr in

  let (tyThis,tIn) =
    match tIn with
      | TTuple(("this",THasTyp([URef(lThis)],_))::tup) ->
          (* ([("this", tyRef lThis)], TTuple tup) *)
          ([("this", tyRef lThis)], TTuple tup)
      | _ ->
          ([], tIn) in

  let (lArgs,cArgs) = (freshVar "Largs", freshVar "cArgs") in

  let formalSubst = [(x, wVar cArgs)] in

(*
  (* NOTE: would like to _not_ substitute away tuple binders, but am
     doing it for now. see 11/27/11 notes.txt entry. *)
  let formalSubst = formalSubst @ depTupleSubst tIn (wVar c_args) in
  let (tIn,(inH,inC)) = expandAwayDepTuples (tIn,(inH,inC)) in
*)

  fpr oc_desugar_hint "formalSubst:\n%s\n"
    (String.concat "" (List.map (fun (x,w) -> spr "  %s |-> %s\n"
       x (prettyStrWal w)) formalSubst));

  let argsCell  = (LocVar lArgs, HConc (cArgs, tIn)) in

  let subst = (formalSubst, [], [], []) in
  let inC   = snd (masterSubstHeap subst ([],inC)) @ [argsCell] in
  let outC  = snd (masterSubstHeap subst ([],outC)) @ [] in
  let tRet  = masterSubstTyp subst tRet in

  (* let tyArgs = [("arguments", tyRef (LocVar lArgs))] in *)
  let tyArgs = [("arguments", tyRef (LocVar lArgs))] in

  ((ts, ls @ [lArgs], hs),
   freshVar "_",
   TTuple (tyThis @ tyArgs), (inH,inC),
   tRet, (outH,outC))

let dsArrowWithoutArgsArray arr =
  let arr = ParseUtils.maybeAddHeapPrefixVar arr in
  arr

let dsArrow arr =
  if !Settings.doArgsArray
  then dsArrowWithArgsArray arr
  else dsArrowWithoutArgsArray arr

(* TODO desugar variables to add __ *)
let dsTyp t env =
  let fTT = function
    | UArr(arr) -> UArr (dsArrow arr)
    | u         -> u in
  let t = mapTyp ~fTT t in
(*
  let t = if !Settings.monotonicHeaps then threadStuffThrough env t else t in
*)
  t

let desugarTypHint hint env =
  (* let err x = printParseErr (spr "desugarScm\n\n%s\n\n%s" cap x) in *)
  match maybeParseTcFail hint with
    | Some(s) -> Log.printParseErr "TODO DJS failure annotations not implemented"
    | None -> begin
        fpr oc_desugar_hint "%s\n" (String.make 80 '-');
        fpr oc_desugar_hint "hint: [%s]\n\n" hint;
        let t = parseTyp hint in
        let t' = dsTyp t env in
        if t <> t' then fpr oc_desugar_hint "%s\n\n" (prettyStr strTyp t');
        t'
      end

let desugarCtorHint hint env =
  let arr = parseCtorTyp hint in
  dsTyp (THasTyp ([UArr arr], PTru)) env
  (* TODO track constructors differently in env *)

(* TODO for now, not allowing intersections of arrows *)
let hasThisParam = function
(*
  | THasTyp(UArr(_,_,TTuple(("this",_)::_),_,_,_)) -> true
*)
  | THasTyp([UArr(_,_,TTuple(("this",_)::_),_,_,_)],PTru) -> true
  | _ -> false

(*
let dsHeap (hs,cs) =
  (hs, List.map (fun (l,hc) ->
         (l, match hc with
               | HConc(x,t) -> HConc (x, dsTyp t)
               | HConcObj(x,t,l') -> HConcObj (x, dsTyp t, l')
               | HWeakTok(tok) -> HWeakTok tok)) cs)
*)


(***** Misc *******************************************************************)

let convertConst = function
  | J.CString(s) -> EVal (VBase (Str s))
  | J.CInt(i)    -> EVal (VBase (Int i))
  | J.CBool(b)   -> EVal (VBase (Bool b))
  | J.CNull      -> EVal (VBase Null)
  | J.CUndefined -> EVal (VBase Undef)
  | J.CNum(f)    -> eVar (spr "_skolem_%d" (Utils.IdTable.process idSkolems f))
  | J.CRegexp _  -> failwith "convert CRegexp"

let eLambda xs e =
  let pat = PNode (List.map (fun x -> PLeaf x) xs) in
  ParseUtils.mkPatFun ([],[],[]) pat e

let eLambdaSimple xs e =
  let pattern = freshVar "pattern" in
  let es =
    Utils.map_i
      (fun x i -> (x, EApp (([],[],[]), eVar "getarg", eStr (string_of_int i))))
      xs in
  let get = ("getarg", EApp (([],[],[]), eVar "get_curried", eVar pattern)) in
  EFun (([],[],[]), pattern, None, ParseUtils.addLets e (get::es))

(*
let eSeq e1 e2 =
  ELet (freshVar "seq", None, e1, e2)
*)

let rec eSeq = function
  | []    -> failwith "eSeq: must call with at least one exp"
  | [e]   -> e
  | e::es -> ELet (freshVar "seq", None, e, eSeq es)

let mkArgsArray es = 
  let l = LocConst (freshVar "argsArray") in
  (l, ENewref (l, ParseUtils.mkTupleExp es))


(***** Prop/Bracket ***********************************************************)

(* rkc: hacked LamJS/exprjs_syntax.ml to distinguish between prop/bracket,
   even though the abstract syntax doesn't. so, need to make sure to undo
   the hack whenever using BracketExpr or PropLValue *)

(* TODO 3/31 instead, just add safe(v) predicate to primitives where needed,
   and ditch the syntactic prop detection *)

(* 3/31: removed this
let undoDotStr s =
  if Str.string_match (Str.regexp "^__dot__\\(.*\\)$") s 0
  then (true, Str.matched_group 1 s)
  else (false, s)
*)
let undoDotStr s = (false, s)

let undoDotExp = function
  | E.ConstExpr (p, J.CString s) ->
      E.ConstExpr (p, J.CString (snd (undoDotStr s)))
  | e -> e

let notAnIntStr s =
  try let _ = int_of_string s in false with Failure _ -> true


(***** Desugaring calls *******************************************************)

let mkApp ?(curried=false) f args =
  if curried then LangUtils.mkApp (eVar f) args
  else begin match args with
    | [x] -> EApp (([],[],[]), eVar f, x)
    | _   -> EApp (([],[],[]), eVar f, (ParseUtils.mkTupleExp args))
  end

let mkCall ts ls func recvOpt args =
  let recv = match recvOpt with Some(e) -> [e] | None -> [] in
  if !Settings.doArgsArray then
    let (locArgs,argsArray) = mkArgsArray args in
    EApp ((ts, ls @ [locArgs], []), 
          func, ParseUtils.mkTupleExp (recv @ [argsArray]))
  else
    EApp ((ts, ls, []), func, ParseUtils.mkTupleExp (recv @ args))


(***** Desugaring expressions *************************************************)

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

  | E.HintExpr (_, h, E.ObjectExpr (p, fields)) when !Settings.fullObjects ->
      (* let (l1,l2) = parseObjLocs h in *)
      let l1 = parseLoc h in
      let obj = freshVar "newObj" in
      let setFields =
        List.map
          (fun (_,k,v) ->
             objOp [] [l1; lObjectPro] "setPropObj"
               [eVar obj; eStr k; ds env v]) fields
      in
      ELet (obj, None, ENewObj (EVal VEmpty, l1, eObjectPro (), lObjectPro),
            eSeq (setFields @ [eVar obj]))

  | E.ObjectExpr (p, fields) when !Settings.fullObjects ->
      let s = freshVar "objLit" in
      ds env (E.HintExpr (p, s, E.ObjectExpr (p, fields)))

  | E.HintExpr (_, h, E.ObjectExpr (p, fields)) -> 
      ENewref (parseLoc h, mkEDict env fields)

  | E.ObjectExpr (p, fields) -> 
      ENewref (LocConst (freshVar "objLit"), mkEDict env fields)

  | E.HintExpr (_, h, E.ArrayExpr (_, es)) when !Settings.fullObjects ->
      let (l,t) = parseArrLit h in
      ENewObj (mkEArray (Some t) env es, l, eArrayPro (), lArrayPro)

  | E.ArrayExpr (_, es) when !Settings.fullObjects ->
      ENewObj (mkEArray None env es, LocConst (freshVar "arrLit"),
               eArrayPro (), lArrayPro)

  | E.HintExpr (_, h, E.ArrayExpr (_, es)) ->
      let (l,t) = parseArrLit h in
      ENewref (l, mkEArray (Some t) env es)

  | E.ArrayExpr (_, es) ->
      ENewref (LocConst (freshVar "arrLit"), mkEArray None env es)

(*
  | E.ThisExpr p -> 
      (* In JavaScript, 'this' is a reserved word.  Hence, we are certain that
         the the bound identifier is not captured by existing bindings. *)
      if !Settings.fullObjects then eVar "this"
      else Log.printParseErr "\"this\" not allowed in djsLite mode"
*)
  (* 4/9 switched to a __this reference cell *)
  | E.ThisExpr p -> EDeref (eVar (dsVar "this"))

  (* TODO 3/15
  | E.IdExpr (p, x) -> let _ = failwith "rkc: ds idexpr" in EVar x
  *)
  | E.IdExpr (p, x) -> ds env (E.VarExpr (p, x))

  | E.VarExpr (p, x) -> begin
      let x = dsVar x in
      (* TODO: IdExpr makes the else clause unnecessary *)
      try 
        if IdMap.find x env.flags then
          (* var-lifting would have introduced a binding for x. *)
          EDeref (eVar x)
        else
          eVar x
      with Not_found ->
        (* TODO *)
        let _ = failwith (spr "rkc: think about top-level VarExpr [%s]" x) in
        mkApp "get" [EDeref (eVar "global"); eStr x]
    end

(** these were the get cases from v0
  | E.BracketExpr (_, E.HintExpr (_, h, e1), e2) when !Settings.fullObjects ->
      let (l1,l2) = parseObjLocs h in
      objGet l1 l2 (ds env e1) (ds env e2)
  | E.BracketExpr (_, e1, e2) ->
      let e2 = undoDotExp e2 in
      mkApp (eVar "get") [EDeref (ds env e1); ds env e2]
**)

  (** for get/set/has, merging the cases for djs and djsLite modes.
      too clever for the djsLite case, but i'm not concerned with
      readability for djsLite desugaring. in particular, the tricky part
      when in djsLite mode is that e2 is undotted right away, so the
      undoDotStr in the CString case will always produce false, so getElem
      will be produced, which is good because there isn't a getProp in
      djsLite.ml. the getProp distinction only becomes necessary and
      useful with prototype-backed arrays. furthermore, objOp appends
      "Lite" when in lite mode. *)

  | E.BracketExpr (_, e1, e2) -> begin
      let (e1Orig,e2Orig) = (e1, e2) in
      let e2 = if !Settings.fullObjects then e2 else undoDotExp e2 in
      let ((ts,ls,hs),e1) =
        match e1 with
          | E.HintExpr (_, h, e1) -> (parseAppArgs h, e1)
          | _                     -> (([],[],[]), e1) in
      if hs <> [] then failwith "x[k] shouldn't have heap args";
      if !Settings.typedDesugaring then begin
        let e1 = ds env e1 in
        let e2 = ds env e2 in
        match getType env e1, getType env e2 with
          | JsObject(l1,l2,_,_), JsInt _ -> Log.printParseErr
                                         "object.integer will definitely fail"
          | JsObject(l1,l2,_,_), JsStr  -> objOp [] [l1;l2] "getPropObj" [e1;e2]
          | JsObject(l1,l2,_,_), _      -> objOp [] [l1;l2] "getPropObj" [e1;e2]
          | JsCtor(_,_,l1,l2), _      -> objOp [] [l1;l2] "getPropObj" [e1;e2]
(*
          | JsProto(_,_,l1,l2), _      -> objOp [] [l1;l2] "getPropObj" [e1;e2]
*)
          | JsArray(t,l1,l2,_,_), JsStr -> objOp [t] [l1;l2] "getPropArr" [e1;e2]
          | JsArray(t,l1,l2,_,_), JsInt _ -> objOp [t] [l1;l2] "getIdx" [e1;e2]
          | JsArray(t,l1,l2,_,_), _     -> objOp [t] [l1;l2] "getElem" [e1;e2]
          | JsTop, JsStr            -> objOp ts ls "getProp" [e1;e2] 
          | JsTop, JsInt _          -> objOp ts ls "getIdx"  [e1;e2] 
          | JsTop, JsTop            -> objOp ts ls "getElem" [e1;e2] 
          (* TODO 4/9 *)
          | JsWeakObj(m), JsStr when !Settings.greedyThaws ->
              (match e1Orig with
                 | E.VarExpr(_,x) ->
                     let loc = LocConst (freshVar "lThaw") in
                     let tmp = freshVar "thawTmp" in
                     let obj = freshVar "thawObj" in
                     let ex = eVar (dsVar x) in
                     let locpro = locProOfWeak "get" m in 
                     ELet (obj, None, ESetref (ex, EThaw (loc, EDeref ex)),
                     ELet (tmp, None, objOp [] [loc;locpro] "getProp" [eVar obj;e2], 
                     ELet (freshVar "seq", None,
                           ESetref (ex, EFreeze (m, Thwd loc, eVar obj)),
                           eVar tmp)))
(*
                     let loc = LocConst (freshVar "lThaw") in
                     let tmp = freshVar "thawTmp" in
                     let ex = eVar (dsVar x) in
                     let locpro = locProOfWeak "get" m in 
                     ELet (freshVar "seq", None, ESetref (ex, EThaw (loc, EDeref ex)),
                     ELet (tmp, None, objOp [] [loc;locpro] "getProp" [e1;e2], 
                     ELet (freshVar "seq", None,
                           ESetref (ex, EFreeze (m, Thwd loc, EDeref ex)),
                           eVar tmp)))
*)
                 (* better to abstract out the functionality above, but for now
                    shoving "this" inside a VarExpr *)
                 | E.ThisExpr p -> ds env (E.BracketExpr (p, E.VarExpr (p, "this"), e2Orig))
                 | _ -> objOp ts ls "getElem" [e1;e2])
          | _ -> objOp ts ls "getElem" [e1;e2]
      end else begin
        match e2 with
          | E.ConstExpr (_, J.CInt i) ->
              objOp ts ls "getIdx" [ds env e1; EVal (vInt i)]
          | E.ConstExpr (_, J.CString s) ->
              let (b,s) = undoDotStr s in
              let f = if b || notAnIntStr s then "getProp" else "getElem" in
              objOp ts ls f [ds env e1; EVal (vStr s)]
          | _ ->
              let e2 = undoDotExp e2 in
              objOp ts ls "getElem" [ds env e1; ds env e2]
      end
    end

  | E.PrefixExpr (_, "prefix:delete", E.BracketExpr (_, ed, ek))
    when !Settings.fullObjects -> begin
      let ((ts,ls,hs),ed) =
        match ed with
          | E.HintExpr (_, h, ed) -> (parseAppArgs h, ed)
          | _                     -> (([],[],[]), ed) in
      if hs <> [] then failwith "delete x[k] shouldn't have heap args";
      let ek = undoDotExp ek in
      match ek with
        | E.ConstExpr (_, J.CInt i) ->
            objOp ts ls "delIdx" [ds env ed; EVal (vInt i)]
        | E.ConstExpr (_, J.CString s) ->
            objOp ts ls "delPropObj" [ds env ed; EVal (vStr s)]
        | _ ->
            objOp ts ls "delElem" [ds env ed; ds env ek]
    end

  | E.PrefixExpr (_, "prefix:delete", E.BracketExpr (_, ed, ek)) ->
      let _ = failwith "djsLite delete" in
      let ek = undoDotExp ek in
      let x = freshVar "del" in
      ELet (x, None, ds env ed,
            ESetref (eVar x, mkApp "del" [EDeref (eVar x); ds env ek]))

  | E.PrefixExpr (_, "prefix:delete", _) ->
      Log.printParseErr "delete not applied to property"

  | E.PrefixExpr (_, "prefix:typeof", e) ->
      (* going through mkTupleExp since typ/loc inference looks for tuples *)
      EApp (([],[],[]), eVar "js_typeof", ParseUtils.mkTupleExp [ds env e])

  | E.PrefixExpr (_, op, e) ->
      let e0 =
        match op with
          (* | "prefix:typeof" -> "js_typeof" *)
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
      (* TODO could add the typedDesugaring stuff here *)
      match ek with
        | E.ConstExpr (_, J.CInt i) ->
            objOp ts ls "hasIdx" [ds env ed; EVal (vInt i)]
        | E.ConstExpr (_, J.CString s) ->
            let f = if notAnIntStr s then "hasProp" else "hasElem" in
            objOp ts ls f [ds env ed; EVal (vStr s)]
        | _ ->
            objOp ts ls "hasElem" [ds env ed; ds env ek]
    end

(** this was the lite case from v0
  | E.InfixExpr (_, "in", ek, ed) ->
      mkApp (eVar "mem") [EDeref (ds env ed); ds env ek]
**)

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

  (* TODO for freeze and thaw, figure out how to handle this (_this) and
     other formals, which aren't ref cells so can't setref *)

  | E.SeqExpr (_, E.HintExpr (_, h, E.ConstExpr (_, J.CString "#freeze")), e2)
        when !Settings.typedDesugaring ->
      let (x,l,thaw) = parseFreeze h in
      let x = dsVar x in
      let env = updateVarType env x l in
      eSeq [ESetref (eVar x, EFreeze (l, thaw, EDeref (eVar x))); ds env e2]

  | E.HintExpr (_, h, E.ConstExpr (_, J.CString "#freeze")) ->
      let (x,l,thaw) = parseFreeze h in
      let x = eVar (dsVar x) in
      ESetref (x, EFreeze (l, thaw, EDeref x))

  | E.SeqExpr (_, E.HintExpr (_, h, E.ConstExpr (_, J.CString "#thaw")), e2)
        when !Settings.typedDesugaring ->
      let (x,l) = parseThaw h in
      let x = dsVar x in
      let env = updateVarType env x l in
      eSeq [ESetref (eVar x, EThaw (l, EDeref (eVar x))); ds env e2]

  | E.HintExpr (_, h, E.ConstExpr (_, J.CString "#thaw")) ->
      let (x,l) = parseThaw h in
      let x = eVar (dsVar x) in
      ESetref (x, EThaw (l, EDeref x))

(*
  | E.AssignExpr (_,
      E.VarLValue (_, x), E.HintExpr (_, h, E.ConstExpr (_, J.CString s)))
    when s = "#freeze" || s = "#thaw" || s = "#refreeze" ->
      (* TODO this still doesn't work, because of desugaring formals
         doesn't get wrapped in a ref... *)
      let x = if x = "_this" then eVar "this" else eVar (dsVar x) in
      (* let x = eVar (dsVar x) in *)
      let l = parseLoc h in
      ESetref (x,
        match s with
          | "#freeze"   -> EFreeze (l, Frzn, EDeref x) (* TODO *)
          | "#thaw"     -> EThaw (l, EDeref x)
          | "#refreeze" -> ERefreeze (l, EDeref x)
          | _           -> Log.printParseErr "freeze/thaw/refreeze impossible")
*)

  | E.AssignExpr (_, E.VarLValue (_, x), e) -> 
      let x = dsVar x in
      if IdMap.mem x env.flags then (* assume var-bound *)
        ESetref (eVar x, ds env e)
      else
        let _ = failwith (spr "assignexpr global [%s]" x) in
        ESetref (eVar "global",
                 mkApp "set" [EDeref (eVar "global"); eStr x; ds env e])

(** these were the get cases from v0
  | E.AssignExpr (_, E.PropLValue (_, E.HintExpr (_, h, e1), e2), e3)
    when !Settings.fullObjects -> 
      let (l1,l2) = parseObjLocs h in
      objSet l1 l2 (ds env e1) (ds env e2) (ds env e3)
  | E.AssignExpr (_, E.PropLValue (_, e1, e2), e3) -> 
      let e2 = undoDotExp e2 in
      let x = freshVar "obj" in
      ELet (x, None, ds env e1,
            ESetref (eVar x, mkApp (eVar "set") [EDeref (eVar x);
                                                 ds env e2; 
**)

(*
  (* 4/3 adding a special sequence case to strongly update the
     Foo.prototype object of a constructor Foo.
     TODO this case is obviously redo-ing a bunch of work, but
     no matter. *)
  | E.SeqExpr (_, E.AssignExpr (p1, E.PropLValue (p2, e1, e2), e3), eNext)
        when !Settings.typedDesugaring &&
             isJsProto (getType env (ds env e1)) ->
      begin match getType env (ds env e1), e2, ds env e3 with
        | JsProto(f,_,_,_),
          E.ConstExpr (_, J.CString newField),
          EAs(_,_,([h],([h'],[]),(t,([h''],[])))) when h = h' && h = h'' ->
          (* this should handle function types and constants wrapped with dsAssert *)
            let env' = updateProtoType f newField t env in
            let e123 = E.AssignExpr (p1, E.PropLValue (p2, e1, e2), e3) in
            eSeq [ds env e123; ds env' eNext]
        | _ ->
            let _ = failwith "no" in
            let e123 = E.AssignExpr (p1, E.PropLValue (p2, e1, e2), e3) in
            eSeq [ds env e123; ds env eNext]
    end
*)

  | E.AssignExpr (_, E.PropLValue (_, e1, e2), e3) -> begin
      let e1Orig = e1 in
      let e2 = if !Settings.fullObjects then e2 else undoDotExp e2 in
      let ((ts,ls,hs),e1) =
        match e1 with
          | E.HintExpr (_, h, e1) -> (parseAppArgs h, e1)
          | _                     -> (([],[],[]), e1) in
      if hs <> [] then failwith "x[k] = y shouldn't have heap args";
      if !Settings.typedDesugaring then begin
        let e1 = ds env e1 in
        let e2 = ds env e2 in
        let e3 = ds env e3 in
        match getType env e1, getType env e2 with
          | JsObject(l1,l2,_,_), JsInt _ -> Log.printParseErr
                                         "object.integer will definitely fail"
          | JsObject(l1,l2,_,_), JsStr  -> objOp [] [l1;l2] "setPropObj" [e1;e2;e3]
          | JsObject(l1,l2,_,_), _      -> objOp [] [l1;l2] "setPropObj" [e1;e2;e3]
          | JsCtor(_,_,l1,l2), _      -> objOp [] [l1;l2] "setPropObj" [e1;e2;e3]
(*
          | JsProto(_,_,l1,l2), _      -> objOp [] [l1;l2] "setPropObj" [e1;e2;e3]
*)
          | JsArray(t,l1,l2,_,_), JsStr -> objOp [t] [l1;l2] "setPropArrLen" [e1;e2;e3]
          | JsArray(t,l1,l2,_,_), JsInt _ -> objOp [t] [l1;l2] "setIdx" [e1;e2;e3]
          | JsArray(t,l1,l2,_,_), _     -> objOp [t] [l1;l2] "setElem" [e1;e2;e3]
          | JsTop, JsStr            -> objOp ts ls "setProp" [e1;e2;e3] 
          | JsTop, JsInt _          -> objOp ts ls "setIdx"  [e1;e2;e3] 
          | JsTop, JsTop            -> objOp ts ls "setElem" [e1;e2;e3] 
          (* 4/9 *)
          | JsWeakObj(m), JsStr when !Settings.greedyThaws ->
              (match e1Orig with
                 | E.VarExpr(_,x) ->
                     let loc = LocConst (freshVar "lThaw") in
                     let tmp = freshVar "thawTmp" in
                     let obj = freshVar "thawObj" in
                     let rhs = freshVar "thawRhs" in
                     let ex = eVar (dsVar x) in
                     let locpro = locProOfWeak "set" m in 
                     ELet (rhs, None, e3,
                     ELet (obj, None, ESetref (ex, EThaw (loc, EDeref ex)),
                     ELet (tmp, None, objOp [] [loc;locpro] "setProp" [eVar obj;e2;eVar rhs], 
                     ELet (freshVar "seq", None,
                           ESetref (ex, EFreeze (m, Thwd loc, eVar obj)),
                           eVar tmp))))
(*
                     let loc = LocConst (freshVar "lThaw") in
                     let tmp = freshVar "thawTmp" in
                     let ex = eVar (dsVar x) in
                     let locpro = locProOfWeak "set" m in 
                     ELet (freshVar "seq", None, ESetref (ex, EThaw (loc, EDeref ex)),
                     ELet (tmp, None, objOp [] [loc;locpro] "setProp" [e1;e2;e3], 
                     ELet (freshVar "seq", None,
                           ESetref (ex, EFreeze (m, Thwd loc, EDeref ex)),
                           eVar tmp)))
*)
                 (* better to abstract out the functionality above, but for now
                    shoving "this" inside a VarExpr *)
(* TODO
                 | E.ThisExpr p -> ds env (E.BracketExpr (p, E.VarExpr (p, "this"), e2Orig))
*)
                 | _ -> objOp ts ls "getElem" [e1;e2])
          | _                       -> objOp ts ls "setElem" [e1;e2;e3] 
      end else begin
        match e2 with
          | E.ConstExpr (_, J.CInt i) ->
              objOp ts ls "setIdx" [ds env e1; EVal (vInt i); ds env e3]
          | E.ConstExpr (_, J.CString s) ->
              let (b,s) = undoDotStr s in
              let f = if b || notAnIntStr s then "setProp" else "setElem" in
              objOp ts ls f [ds env e1; EVal (vStr s); ds env e3]
          | _ ->
              let e2 = undoDotExp e2 in
              objOp ts ls "setElem" [ds env e1; ds env e2; ds env e3]
      end
    end

  | E.LetExpr (_, x, e1, e2) ->
      let x = dsVar x in
      ELet (x, None, ds env e1, ds (addFlag x false env) e2)

  (* rkc: catching VarDeclExpr within SeqExpr so i can turn it into a
       normal let-binding instead of doing var lifting or implicit
       updates to global *)

(*
  (* rkc TODO figure out what annotation for x should be *)
  | E.SeqExpr (_, E.HintExpr (_, s, E.VarDeclExpr (p1, x, xInit)), e) ->
    begin
      (match xInit with
         | E.ConstExpr (_, J.CUndefined) -> ()
         | _ -> printParseErr "EJS should've set HintVarDecl init to undef"
      );
      failwith "hint var"
    end
*)

  | E.SeqExpr (_,
      E.VarDeclExpr (_, x,
        E.HintExpr (_, s, E.ConstExpr (_, J.CString "#extern"))), e2) ->
      (* TODO could addVarType here for Ref(lObjectProto) *)
      let x = dsVar x in
      EExtern (x, desugarTypHint s env, ds (addFlag x false env) e2)

(*
  | E.SeqExpr (_,
      E.AssignExpr (_, E.PropLValue (_, obj, key),
        E.HintExpr (_, s, E.ConstExpr (_, J.CString "#extern"))), e2) ->
      failwith "TODO"
*)

  | E.SeqExpr (_, E.HintExpr (_, s, E.ConstExpr (_, J.CString "#weak")), e2) ->
      let (m,t,l) = parseWeakLoc s in
      (* TODO store weak locs differently in env *)
      let _ = weakLocs := (m,l) :: !weakLocs in
      EWeak ((m, dsTyp t env, l), ds env e2)

  (* rkc: 3/15 match this case if i wanted to look for recursive functions as
         var fact = function f(n) /*: ... */ {};
  | E.SeqExpr (_,
      E.VarDeclExpr (_, x, E.HintExpr (_, s, E.FuncStmtExpr (p, f, args, body))), e2) ->
      printParseErr "good"
  *)

  | E.SeqExpr (_, E.VarDeclExpr (_, x, e), e2) -> begin
      let (lo,e) =
        match e with
          | E.HintExpr (_, s, (E.ConstExpr (_, J.CUndefined) as eUndef)) ->
               (Some (parseLoc s), eUndef)
          | _ ->
               (None, e) in

      if IdMap.mem x env.flags then (* x is local variable *)
        (if !Settings.doVarLifting (* do what LamJS normally does *)
         then eSeq [dsVarDeclOrig env x e; ds env e2]
         else dsVarDecl env x lo e e2)

      else (* x is declared at the top-level scope *)
        (if !Settings.doImplicitGlobal (* do what LamJS normally does *)
         then eSeq [dsVarDeclOrig env x e; ds env e2]
         else dsVarDecl env x lo e e2)
    end

  | E.VarDeclExpr _ -> Log.printParseErr "ds VarDeclExpr: shouldn't get here"

  | E.SeqExpr (_, E.HintExpr (_, s, E.FuncStmtExpr (p, f, args, body)), e2)
    when !Settings.fullObjects ->
      let fOrig = f in
      let f = dsVar f in
(*
      let code =
        EAs ("DjsDesugarCtor",
             dsFunc true env p args body,
             s |> desugarCtorHint |> ParseUtils.typToFrame) in
*)
      let t = desugarCtorHint s env in
      let env = addFormals t env in

      (* 4/9: unfortunate that have to call addFlag here, since dsFunc does
         it too *)
      let env = List.fold_left (fun env arg -> addFlag arg true env) env args in
      let t = augmentType t env (fvExps "dsFuncExpr recursive" env [body]) in

      let code =
        EAs ("DjsDesugarCtor", dsFunc true env p args body,
             ParseUtils.typToFrame t) in
      let proto =
        ENewObj (EVal VEmpty, LocConst (spr "l%sProto" fOrig),
                 eObjectPro (), lObjectPro) in

      (* in v0, i used simple objects for ctor function objects
      let obj =
        ENewref (LocConst (spr "&%s_obj" fOrig),
                 EDict [(eStr "code", code);
                        (eStr "prototype", proto)]) in
      (* adding f after dsFunc, since ctor shouldn't be recursive *)
      let env = IdMap.add f true env in

      ELet (f, None, ENewref (LocConst (spr "&%s" fOrig), obj), ds env e2)
      *)

      let xObj = freshVar "ctorObj" in
      let eObj = eVar xObj in
      let lObj = LocConst (spr "l%sObj" fOrig) in
      let freshObj =
        ENewObj (EVal VEmpty, lObj, eFunctionPro (), lFunctionPro) in
      let setCode =
        objOp [] [lObj; lFunctionPro]
          "setPropObj" [eObj; eStr "code"; code] in
      let setProto =
        objOp [] [lObj; lFunctionPro]
          "setPropObj" [eObj; eStr "prototype"; proto] in

      let env = addFlag f true env in
      let env = addCtorType f t env in

      ELet (xObj, None, freshObj,
      ELet (freshVar "setCode", None, setCode,
      ELet (freshVar "setProto", None, setProto,
      ELet (f, None, ENewref (LocConst (spr "&%s" fOrig), eObj),
            ds env e2))))

(*
  (* rkc: turning this into a letrec *)
  | E.SeqExpr (_, E.HintExpr (_, s, E.FuncStmtExpr (p, f, args, body)), e2) ->
    begin
      printParseErr "djsDesugar 11/27: letrec"
(*
      let (scm,wrapE) = desugarHint s in
      let env = IdMap.add f false env in
      (* TODO is this right place to wrap? try polymorphic rec fun. *)
      let e1 = wrapE (dsFunc env p args body) in
      let e2 = ds env e2 in
      ParseUtils.mkLetRec f scm e1 e2
*)
    end
*)

  (* rkc: the original LamJS case *)
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
      if !Settings.augmentHeaps then begin
        match e2 with
          | E.LabelledExpr(_,cl,body) when isContLabel cl ->
              dsWhile env bl cl test body dummyFrame
          | E.SeqExpr(_,E.LabelledExpr(_,cl,body),incr) when isContLabel cl ->
              dsFor env bl cl test body incr dummyFrame
          | _ ->
              Log.printParseErr "desugar EJS unannotated while fail"
(*
      end else if !Settings.inferFrames then begin
        let _ = failwith "-augmentHeaps is now the way to go" in
        match e2 with
          | E.LabelledExpr(_,cl,body) when isContLabel cl ->
              dsWhile env bl cl test body (envToFrame env [test;body])
          | E.SeqExpr(_,E.LabelledExpr(_,cl,body),incr) when isContLabel cl ->
              dsFor env bl cl test body incr (envToFrame env [test;body;incr])
          | _ ->
              Log.printParseErr "desugar EJS unannotated while fail"
*)
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

(*
  | ForInExpr (p, x, obj, body) ->
      EFix
        (p,
         [ ("%forin",
            ELambda 
              (p, [x],
               (* TODO: Infinite loop below, but adequate for typing *)
               ESeq (p, ds_expr env body,
                     EApp (p, EId (p, "%forin"), [])))) ],
         EApp (p, EId (p, "%forin"), []))

*)

  (* rkc: fall through to original Lam JS case *)
  | E.LabelledExpr (_, l, e) -> ELabel (trimLabel l, None, ds env e)

  | E.BreakExpr (_, l, e) -> EBreak (trimLabel l, ds env e)

(** these were the get cases from v0
  | E.AppExpr (p, E.HintExpr (_, s, E.BracketExpr (p', obj, prop)), args)
    when !Settings.fullObjects ->
      let (ts,ls,hs) = parseAppArgs s in
      let (l1,l2) =
        match ls with
          | l1::l2::_ -> (l1, l2)
          | _ -> printParseErr "ds method call: requires >=2 loc args"
      in
      let obj = ds env obj in
      let (locArgs,argsArray) = mkArgsArray (List.map (ds env) args) in
      let func = objGet l1 l2 obj (ds env prop) in
      EApp ((ts, ls @ [locArgs], hs), func, 
            ParseUtils.mkTupleExp [obj; argsArray])
  | E.AppExpr (p, E.BracketExpr (p', obj, prop), args) ->
      if !Settings.fullObjects
      then printParseErr "method call must be annotated"
      else printParseErr "method call not allowed in djsLite mode"
**)

  | E.AppExpr (_, E.VarExpr (_, "assert"), es) -> begin
      match es with
        | [E.HintExpr (_, s, e)] -> dsAssert env s e
        | [e]                    -> dsAssert env "{(= v true)}" e
        | _                      -> Log.printParseErr "bad assert syntax"
    end

  | E.AppExpr (_, E.HintExpr (_, _, E.BracketExpr _), _)
    when not !Settings.fullObjects ->
      Log.printParseErr "method call not allowed in djsLite mode"

  | E.AppExpr (p, E.BracketExpr (_, f, E.ConstExpr (_, J.CString s)), obj::args)
        when snd (undoDotStr s) = "apply" ->
      mkCall [] [] (ds env f) (Some (ds env obj)) (List.map (ds env) args)

  | E.AppExpr (p, E.HintExpr (_, s, E.BracketExpr (p', obj, prop)), args) ->
    begin
      let (ts,ls,hs) = parseAppArgs s in
      if hs <> [] then failwith "x[k] shouldn't have heap args";
      dsMethCall env ts ls obj prop args 
    end

  | E.AppExpr (p, E.BracketExpr (p', obj, prop), args) ->
      dsMethCall env [] [] obj prop args 

(*
  | E.AppExpr (_, E.BracketExpr _, _) when not !Settings.fullObjects ->
      Log.printParseErr "method call not allowed in djsLite mode"
*)

  (*
  | E.AppExpr (p, E.HintExpr(_,"apply",f), obj::args) ->
      let (locArgs,argsArray) = mkArgsArray (List.map (ds env) args) in
      EApp (([], [] @ [locArgs], []),
            ds env f,
            ParseUtils.mkTupleExp [ds env obj; argsArray])
  *)

  | E.AppExpr (p, f, args) ->
      let (f,(ts,ls,hs)) =
        match f with
          | E.HintExpr(_,h,f) -> (f, parseAppArgs h)
          | _                 -> (f, ([],[],[])) in
      let _ = if hs <> [] then Log.printParseErr "why passing heap args" in
      mkCall ts ls (ds env f) None (List.map (ds env) args)

  | E.NewExpr (_, E.HintExpr (_, s, constr), args)-> begin
      if !Settings.fullObjects = false then
        Log.printParseErr "new not allowed in djsLite mode";

      (* v0 treated constructors as simple objects
      (* could save a couple let-bindings by factoring get (!funcObj) *)
      let funcObj = ds env constr in
      let ctor = mkApp (eVar "get") [EDeref funcObj; eStr "code"] in
      let proto = mkApp (eVar "get") [EDeref funcObj; eStr "prototype"] in
      *)

      (* providing at least the lFunctionProto loc param, the other will
         be inferred *)
      let funcObj = ds env constr in
      let ctor =
        objOp [] [lFunctionPro] "getPropObj" [funcObj; eStr "code"] in
      let proto =
        objOp [] [lFunctionPro] "getPropObj" [funcObj; eStr "prototype"] in

      let ((ts,ls,hs),lProto) = parseNew s in
      let lObj =
        match ls with
          | lObj::_ -> lObj
          | _ -> Log.printParseErr "new annot: must have at least 1 loc arg"
      in
      let obj = ENewObj (EVal VEmpty, lObj, proto, lProto) in
      mkCall ts ls ctor (Some obj) (List.map (ds env) args)
    end

  | E.NewExpr _ ->
      if !Settings.fullObjects
      then Log.printParseErr "new must have annotations"
      else Log.printParseErr "new not allowed in djsLite mode"

  (* rkc: LamJS desugaring normally writes to a non-existent reference *)
  (* | FuncStmtExpr (p, f, args, body) -> *)
  (*    EOp2 (p, SetRef, EId (p, f), ds_expr env (FuncExpr (p, args, body))) *)

  (* rkc: LamJS desugaring normally discards hints *)
  (* | HintExpr (_, _, e) -> ds_expr env e *)

  | E.FuncExpr (_, args, _) ->
      Log.printParseErr (spr
        "function expression with formals [%s] not annotated"
           (String.concat ", " args))

  | E.HintExpr (_, s, E.FuncStmtExpr (p, f, args, body)) ->
      let t = desugarTypHint s env in
      let f = dsVar f in
      let env = addFlag f false env in
      let env = addFormals t env in
      (* 4/9: unfortunate that have to call addFlag here, since dsFunc does
         it too
      *)
      let env = List.fold_left (fun env arg -> addFlag arg true env) env args in
      let env = if hasThisParam t then addFlag "this" true env else env in
      let t = augmentType t env (fvExps "dsFuncExpr recursive" env [body]) in
(*
      let func = dsFunc false env p args body in
*)
      let func = dsFunc (hasThisParam t) env p args body in
      EApp (([t],[],[]), eVar "fix",
        EFun (([],[],[]), f, None, func))

  | E.FuncStmtExpr (_, f, _, _) ->
      Log.printParseErr (spr "function statement [%s] not annotated" f)

  | E.HintExpr (_, s, e) -> dsAssert env s e

  | E.ThrowExpr _ -> failwith "throwexpr"
  | E.TryFinallyExpr _ -> failwith "try finally"
  | E.TryCatchExpr _ -> failwith "try catch"

(*
  | TryCatchExpr (p, body, x, catch) ->
      ETryCatch (p, ds_expr env body, ELambda (p, [x], ds_expr env catch))
  | TryFinallyExpr (p, e1, e2) -> 
      ETryFinally (p, ds_expr env e1, ds_expr env e2)
  | ThrowExpr (p, e) -> EThrow (p, ds_expr env e)
*)

and mkEDict env fields =
  EDict (List.map (fun (_, x, e) -> (eStr x, ds env e)) fields)

and mkEArray topt env es =
  let t = match topt with Some(t) -> t | None -> tyArrDefault in
  EArray (t, List.map (ds env) es)

(* for FuncExprs, this is an annotation.
   for all other expressions, it's an assert *)
and dsAssert env s e =
  let (e,t) =
    match e with
      | E.FuncExpr(p,args,body) ->
          let t = desugarTypHint s env in
          let env = addFormals t env in

          let env = List.fold_left (fun env arg -> addFlag arg true env) env args in

          let t = augmentType t env (fvExps "dsFuncExpr" env [body]) in
          (dsFunc (hasThisParam t) env p args body, t)
      | _ ->
          (ds env e, desugarTypHint s env)
  in
  EAs ("DjsDesugar", e, ParseUtils.typToFrame t)
(*
  let x = freshVar "hint" in
  ELet (x, Some frame, e, eVar x)
*)

and dsMethCall env ts ls obj prop args =
  let obj = ds env obj in
  (* TODO could add the typedDesugaring stuff here *)
  let func =
    match prop with
      | E.ConstExpr (_, J.CString s) ->
          let (b,s) = undoDotStr s in
          let f = if b || notAnIntStr s then "getProp" else "getElem" in
          objOp ts ls f [obj; EVal (vStr s)]
      | _ ->
          let prop = undoDotExp prop in
          objOp ts ls "getElem" [obj; ds env prop]
  in
 (* TODO for now, just passing the same poly args, but this probably
    will not work in general *)
  mkCall ts ls func (Some obj) (List.map (ds env) args)

and dsFunc thisParam env p args body =
  if !Settings.doArgsArray
  then dsFuncWithArgsArray thisParam env p args body
  else dsFuncWithoutArgsArray thisParam env p args body

(* 3/30 *)
and dsFuncWithoutArgsArray thisParam env p args body =
  (* 4/9: starting to use a __this reference cell to facilitate thaw/freeze *)
  let args = if thisParam then ("this"::args) else args in
  let env =
    List.fold_left (fun env x -> addFlag (dsVar x) true env) env args in
  let body =
    List.fold_left (fun acc x ->
      let _x = dsVar x in
      ELet (_x, None, ENewref (LocConst (spr "&%s" x), eVar x), acc)
    ) (ds env body) args in
  eLambdaSimple args body
(*
  if thisParam
    then eLambdaSimple ("this"::args) body
    else eLambdaSimple args body
*)

(* rkc: based on LamJS E.FuncExpr case *)
and dsFuncWithArgsArray thisParam env p args body =
  failwith "dsFuncWithArgsArray: update this to __this";
  let args = List.map dsVar args in
  let init_var x exp =
(*
    failwith "init_var: what is this?";
*)
    ELet (x, None, ENewref (LocConst (freshVar "freshLoc"), EVal vUndef), exp)
  and get_arg x n exp =
    (*
    ELet (x, None,
          (* ENewref (freshVar "freshLoc", *)
          ENewref (LocConst (spr "&%s" x),
                   mkApp (eVar "get")
                      [EDeref (eVar "arguments");
                       EVal (vStr (string_of_int n))]),
          exp) 
    *)
    (* 11/28: manually doing ANF here so can play the trick with the
       original source binder x, using it as the initial value for the
       pointer variable __x. *)
    let xOrig = undoDsVar x in
    ELet (xOrig, None, mkApp "getarg" [eStr (string_of_int n)],
    ELet (x, None, ENewref (LocConst (spr "&%s" xOrig), eVar xOrig),
      exp))
  and vars = Exprjs_syntax.locals body in
  (* rkc: adding locals at top of function body only if flag set *)
  (* let env = IdSet.fold (fun x env -> IdMap.add x true env) vars env in *)
  let env =
    if !Settings.doVarLifting
      then IdSet.fold (fun x env -> addFlag x true env) vars env
      else env in
  let env = List.fold_left (fun env x -> addFlag x true env) env args in
  let env = addFlag "arguments" false (addFlag "this" false env) in
  let body = 
    List.fold_right2 get_arg args (Prelude.iota (List.length args))
      (List.fold_right init_var (IdSetExt.to_list vars)
         (ds env body)) in
  (* 11/28: adding "getarg" at the top just once so each get_arg can use it *)
  let body =
    if List.length args = 0 then body
    else ELet ("getarg", None,
               mkApp ~curried:true "get_curried" [EDeref (eVar "arguments")],
               body)
  in
  if thisParam
    then eLambda ["this"; "arguments"] body
    else eLambda ["arguments"] body

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
  then ELabel (breakL, Some frame, fixloop)
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
  then ELabel (breakL, Some frame, fixloop)
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
  then ELabel (breakL, Some frame, fixloop)
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
  then ELabel (breakL, Some frame, fixloop)
  else fixloop

(* rkc: creates a traditional lexically-scoped let-binding to a reference *)
and dsVarDecl env x lo e e2 =
  (* let l = match lo with Some(l) -> l | None -> freshVar x in *)
  let l = match lo with Some(l) -> l | None -> LocConst (spr "&%s" x) in
  let x = dsVar x in
  let e = ds env e in
  let env = addVarType env x e in
  ELet (x, None, ENewref (l, e), ds (addFlag x true env) e2)

  (* could even forgo the ref if a reason should arise ... *)
  (* ELet (x, None, None,
            ds env e,
            ds (IdMap.add x false env) e2) *)

and dsVarDeclOrig env x e =
  Log.printParseErr (spr "dsVarDeclOrig [%s]" x)
(*
  (* rkc: this is the original LamJS case. *)
  | VarDeclExpr (p, x, e) -> 
      let _ = failwith "rkc: original VarDeclExpr case called" in
      if IdMap.mem x env then
        (* var-lifting would have introduced a binding for x. *)
        EOp2 (p, SetRef, EId (p, x), ds_expr env e)
      else 
        let _ = failwith "rkc: think about top-level VarDecl" in
        EOp2 (p, SetRef, EId (p, "[[global]]"),
              EUpdateField (p, EOp1 (p, Deref, EId (p, "[[global]]")),
                            EConst (p, JavaScript_syntax.CString x),
                            ds_expr env e))
*)

let desugar e =
  checkVars e;
  let e = freshenLabels e in
  collectMacros e;
  ds emptyEnv e


(***** Sequencing EJS expressions *********************************************)

(* The JS parser doesn't have a "prelude" production, so this fakes it by
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

