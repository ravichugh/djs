%{

(* ocamlbuilding with -use-menhir flag. differences with ocamlyacc:
    - ocaml comments everywhere
    - multiple patterns for a single action
    - LangParser.Error instead of Parsing.Parse_error
    - the $startpos,$endpos syntax

   lots of refactorings can be done:
    - use built in lists and options
*)


open Lang
open LangUtils
open Settings


(* shadowing failwith, since Failure is getting caught when parsing
   with menhir. use parse_err instead. *)
let failwith = 0

let printParseErr = Log.printParseErr

let eOp1 (s,x)     = mkApp (eVar s) [x]
let eOp2 (s,x,y)   = mkApp (eVar s) [x;y]
let eOp3 (s,x,y,z) = mkApp (eVar s) [x;y;z]

(* make curried lambdas, putting polyFormals on the first lambda *)
let mkCurriedFuns xs e =
  let rec foo = function
    | []    -> printParseErr "mkCurriedFuns: need at least one value var"
    | x::[] -> vFun (PLeaf x, e)
    | x::xs -> vFun (PLeaf x, EVal (foo xs))
  in foo xs

let mkFun p e =
  match p with
    | PLeaf(x) -> mkCurriedFuns [x] e
    | _        -> ParseUtils.mkPatFun p e

(* not using LangUtils.freshVar, since want a version that does not
   insert leading zeroes and does not keep a counter across all freshvars *)
let dummyBinder =
  let c = ref 0 in
  fun () ->
    incr c;
    (* spr "%s_%d" "_dummy" !c *)
    spr "%s_%d" "_underscore" !c

let emp = ([],[])

let mkSimpleSugarTyp s =
  if List.mem_assoc s LangUtils.simpleSugarToTyp
  then List.assoc s LangUtils.simpleSugarToTyp
  else printParseErr (spr "unexpected Sugar: [%s]" s)

let mkSugarTyp x s p =
  match s with (* NOTE: keep these in sync with LangUtils.simpleSugarToTyp *)
    | "Int"  -> TQuick(x,QBase(BInt),p)
    | "Num"  -> TQuick(x,QBase(BNum),p)
    | "Bool" -> TQuick(x,QBase(BBool),p)
    | "Str"  -> TQuick(x,QBase(BStr),p)
    | "Dict" -> TRefinement(x,pAnd[pDict;p])
    | _      -> printParseErr (spr "bad sugar {%s:%s|%s}" x s (strForm p))


(***** Syntactic sugar: "same" ************************************************)

let heapStack : heap list ref = ref []
(* every time a heap is parsed inside a type, push it onto this stack.
   this is used to help expand occurrences of "same" during parsing.
   since every heap is pushed onto this stack, pop two heaps after an
   impure arrow is successfully parsed. *)

let registerHeap h =
  heapStack := h :: !heapStack;
  h

let popDHeap () =
  heapStack := List.tl !heapStack

let copyCell exact x s =
  if exact then valToSingleton (vVar x) else s

let freshenCell exact l = function
  | HStrong(None,s,_,_) -> printParseErr "freshenCell"
  | HStrong(Some(x),s,lo,_) -> (* not carrying cloinv to output heap *)
      let xo = if exact then None else Some (freshVar x) in 
      HStrong (xo, copyCell exact x s, lo, None)
  | HWeak(tok) -> HWeak tok

let sameHeap exact =
  let (hs,cs) = List.hd !heapStack in
  let cs = List.map (fun (l,hc) -> (l, freshenCell exact l hc)) cs in
  (hs, cs)

let sameCell exact l =
  try freshenCell exact l (List.assoc l (snd (List.hd !heapStack)))
  with
    Not_found ->
    printParseErr (spr "sameCell: [%s] not found in previous heap" (strLoc l))
  | Failure("hd") ->
    printParseErr "sameCell: empty heap"


(***** Syntactic sugar: "x:Ref", "x:Ref?", "x.pro", "cur" *********************)

let tyAnonRef = tyTypTerm (URef (LocConst "Ref"))
let tyAnonMaybeRef = tyTypTerm (URef (LocConst "Ref?"))
let curHeap = "Cur"

let replaceCurInHeap hvar (hs,cs) =
  let hs = List.map (fun h -> if h = curHeap then hvar else h) hs in
  (hs, cs)

let replaceCurInForm hvar = function
  | PHeapHas(h,l,k)   -> PHeapHas (replaceCurInHeap hvar h, l, k)
  | PObjHas(ds,k,h,l) -> PObjHas (ds, k, replaceCurInHeap hvar h, l)
  | p                 -> p

let replaceCurInWal hvar = function
  | WHeapSel(h,l,k)   -> WHeapSel (replaceCurInHeap hvar h, l, k)
  | WObjSel(ds,k,h,l) -> WObjSel (ds, k, replaceCurInHeap hvar h, l)
  | w                 -> w

let expandHeapLocSugar (arr: uarrow) : uarrow =

  let arr = ParseUtils.maybeAddHeapPrefixVar arr in
  let ((ts,ls,hs),xArg,t1,h1,t2,h2) = arr in

  let locSubst = ref [] in
  let addToSubst y ly =
    if not (List.mem_assoc y !locSubst) then locSubst := (y,ly) :: !locSubst in

  (* collect the x's such that x:Ref or x:Ref? appear in input tuple type
     and generate a correspond Lx variable *)
  let t1 =
    match t1 with
      | TQuick("v",QTuple(tup,false),p) when p = pTru ->
          let tup =
            List.map (function
              | Some(y), s when s = tyAnonRef ->
                  let ly = spr "L%s" y in
                  let _ = addToSubst y ly in
                  (Some y, tyRef (LocVar ly))
              | Some(y), s when s = tyAnonMaybeRef ->
                  let ly = spr "L%s" y in
                  let _ = addToSubst y ly in
                  (Some y, TMaybeNullRef (LocVar ly, pTru))
              | yo, s ->
                  (yo, s)
            ) tup
          in
          TQuick ("v", QTuple (tup, false), pTru)
      | _ ->
          t1 in
  
  (* for each x computed above, map each use of x in a location position to Lx.
     also, for each occurrence of x.pro location position, generate a fresh Lxpro
     and map x.pro to Lxpro. *)
  let fLoc = function
    | LocConst(y) when List.mem_assoc y !locSubst ->
        LocVar (List.assoc y !locSubst)
    | LocConst(y) when Str.string_match (Str.regexp "^\\(.*\\)[.]pro$") y 0 ->
        let y_prefix = Str.matched_group 1 y in
        if List.mem_assoc y_prefix !locSubst then
          let lypro = spr "L%spro" y_prefix in
          let _ = addToSubst y lypro in
          LocVar lypro
        else
          LocConst y
    | LocConst(y) when Str.string_match (Str.regexp "^.*[.].*$") y 0 ->
        printParseErr (spr "location identifier [%s] contains a \".\" \
          that isn't part of a \".pro\" location" y)
    | LocConst(y) -> LocConst y
    | LocVar(y) -> LocVar y in

  let (t1,t2) = (mapTyp ~fLoc t1, mapTyp ~fLoc t2) in
  let (h1,h2) = (mapHeap ~fLoc h1, mapHeap ~fLoc h2) in

  (* add the Lx and Lxpro location variables *)
  let ls = ls @ (List.rev (List.map snd !locSubst)) in

  (* replace Cur with the heap variable *)
  let (t1,t2,h1,h2) =
    match hs with
      | [hvar] ->
        (* the intention is that this hvar was added by maybeAddPrefixHeap.
           if the variable was explicitly provided, then could signal an error
           that Cur should not be used. *)
          let (fForm,fWal) = (replaceCurInForm hvar, replaceCurInWal hvar) in
          let (mapTyp,mapHeap) = (mapTyp ~fForm ~fWal, mapHeap ~fForm ~fWal) in
          (mapTyp t1, mapTyp t2, mapHeap h1, mapHeap h2)
      | _ ->
          (t1, t2, h1, h2) in

  ((ts,ls,hs), xArg, t1, h1, t2, h2)


(******************************************************************************)

%}

%token <int> INT
(* %token <float> NUM *)
%token <string> STR
%token <bool> BOOL VBOOL
%token <Lang.vvar> VAR
%token <string> TVAR (* using this for tvar, lvar, and hvar *)
%token <Lang.lbl> LBL
%token <string> SUGAR
%token
  EOF TAG LET (* REC *) EQ IN FUN ARROW IF THEN ELSE
  LPAREN RPAREN LBRACE RBRACE LBRACK RBRACK (* ALL *) (* DOT *) COMMA
  SEMI DCOLON COLON AS GT (* GTGT *) EXTERN FAIL PIPE (* PIPEGT *)
  OR IMP IFF NOT AND ITE HAS SEL UPD EQMOD DOM WBOT EMPTY
  TYPE NULL NULLBOX NEW BANG QMARK
  PLUS MINUS (* MUL *) DIV LT LE GE (* NE EQEQ AMPAMP PIPEPIPE PLUSPLUS *)
  ASSGN NEWREF REFTYPE (* AT *) MAPSTO SAME HEAP
  SAME_TYPE SAME_EXACT CUR
  WEAK FRZN THWD FREEZE THAW
  ARRTYPE PACKED LEN TRUTHY FALSY INTEGER
  BREAK THROW TRY CATCH FINALLY
  UNDEF
  UNDERSCORE TCOLON ELLIPSIS
  HEAPHAS HEAPSEL OBJHAS OBJSEL
  WITH (* BEGIN END *)
  LTUP RTUP BOT

%type <Lang.exp> prog
%type <Lang.exp -> Lang.exp> prelude
%type <Lang.typ> jsTyp
%type <Lang.typs * Lang.locs * Lang.heaps> jsPolyArgs
%type <Lang.loc> jsLoc
%type <Lang.weakloc> jsWeakLoc
%type <Lang.vvar * Lang.loc * Lang.thawstate> jsFreeze
%type <Lang.vvar * Lang.loc> jsThaw
%type <Lang.loc * Lang.loc option> jsObjLocs
%type <Lang.frame> jsWhile
%type <Lang.typterm> jsCtor
%type <Lang.loc * Lang.loc option * (Lang.typs * Lang.locs * Lang.heaps) option> jsNew
%type <Lang.loc * Lang.typ> jsArrLit
%type <Lang.heap> jsHeap
%type <Lang.vvar * Lang.macro> jsMacroDef
%type <string> jsFail

%start prog prelude
%start jsTyp jsPolyArgs jsLoc jsObjLocs jsWhile jsFail jsCtor jsNew jsArrLit
       jsHeap jsFreeze jsThaw jsWeakLoc jsMacroDef

%%

prog : exp EOF     { $1 }

prelude :
 | EOF                                 { fun e -> e }
 | EXTERN x=VAR DCOLON t=typ p=prelude { fun e -> EExtern(x,t,p(e)) }
 | LET x=VAR a=ann EQ e0=exp p=prelude { fun e -> ELet(x,Some(a),e0,p(e)) }
 | LET x=VAR EQ e0=exp p=prelude       { fun e -> ELet(x,None,e0,p(e)) }
 | HEAP LPAREN l=heapenvbindings RPAREN p=prelude
     { fun e -> EHeapEnv(l,p(e)) }

baseval :
 | b=VBOOL         { Bool b }
 | i=INT           { Int i }
 | s=STR           { Str s }
 | UNDEF           { Undef }

value_ :
 | x=baseval       { VBase x }
 | NULL            { VNull }
 | x=VAR           { VVar x }
 | EMPTY           { VEmpty }

 | LPAREN x=value WITH y=value EQ z=value RPAREN { VExtend(x,y,z) } 

value :
 | v=value_        { wrapVal pos0 v }
 | v=lambda        { v }

exp :
 | exp1                                   { $1 }
 | IF exp THEN exp ELSE exp               { EIf($2,$4,$6) }
 | LET x=varopt EQ e1=exp IN e2=exp       { ELet(x,None,e1,e2) }
 | LET x=varopt a=ann EQ e1=exp IN e2=exp { ELet(x,Some(a),e1,e2) }
 (* | LET REC VAR DCOLON scm EQ exp IN exp  { ParseUtils.mkLetRec $3 $5 $7 $9 } *)

 | EXTERN VAR DCOLON typ exp                  { EExtern($2,$4,$5) }
 | HEAP LPAREN l=heapenvbindings RPAREN e=exp { EHeapEnv(l,e) }
 | WEAK w=weakloc e=exp                       { EWeak(w,e) }
 | TYPE x=VAR DCOLON tt=typ_term e=exp        { EMacro(x,MacroTT(tt),e) }
 | TYPE x=VAR EQ t=typ e=exp                  { EMacro(x,MacroT(t),e) }

 | x=LBL LBRACE e=exp RBRACE             { ELabel(x,e) }
 | BREAK LBL exp                         { EBreak($2,$3) }

 | THROW exp                             { EThrow($2) }
 | TRY LBRACE exp RBRACE
   CATCH LPAREN VAR RPAREN
   LBRACE exp RBRACE                     { ETryCatch($3,$7,$10) }
 | TRY LBRACE exp RBRACE
   FINALLY LBRACE exp RBRACE             { ETryFinally($3,$7) }

 (* TODO these should only be allowed at the top-level and at the
    beginning, but not checking that right now.
    Main.parseProgAndExpand makes these assumptions. so, better
    to make prog production return (directives, exp) *)
 | x=LBL s=STR e=exp                     { if x = "use" then ELoadSrc(s,e)
                                           else printParseErr
                                             (spr "unknown directive [%s]" x) }

exp1 :
 | exp2                          { $1 }
 | BANG e=exp2                   { EDeref(e) }
 | e1=exp1 ASSGN e2=exp2         { ESetref(e1,e2) }

 | e1=exp1 e2=exp2                              { EApp(([],[],[]),e1,e2) }
 | LPAREN l=poly_actuals e1=exp1 RPAREN e2=exp2 { EApp(l,e1,e2) }

 | NEWREF l=loc e=exp2
     { match l with
         | LocConst(x) when x.[0] = '&' -> ENewref(l,e,None)
         | _ -> printParseErr (spr "ref %s isn't an & address" (strLoc l)) }
 | NEWREF LPAREN l=loc COMMA e=exp2 COMMA ci=typ_opt RPAREN
     { match l with
         | LocConst(x) when x.[0] = '&' -> ENewref(l,e,ci)
         | _ -> printParseErr (spr "ref %s isn't an & address" (strLoc l)) }

 | NEW LPAREN e1=exp COMMA l1=loc COMMA e2=exp COMMA l2=loc RPAREN
     { ENewObj(e1,l1,e2,l2,None) }
 | NEW LPAREN e1=exp COMMA l1=loc COMMA e2=exp COMMA l2=loc COMMA ci=typ_opt RPAREN
     { ENewObj(e1,l1,e2,l2,ci) }

 | THAW LPAREN l=loc COMMA e=exp RPAREN                     { EThaw(l,e) }
 | FREEZE LPAREN l=loc COMMA x=thawstate COMMA e=exp RPAREN { EFreeze(l,x,e) }

exp2 :
 | v=value                                   { EVal v }
 | LPAREN exp RPAREN                         { $2 }
 | LPAREN exp COMMA RPAREN                   { ParseUtils.mkTupleExp ($2::[]) }
 | LPAREN exp COMMA exps RPAREN              { ParseUtils.mkTupleExp ($2::$4) }
 | LPAREN FAIL STR exp RPAREN                { ETcFail($3,$4) }
 (* | LPAREN e=exp RPAREN AS f=frame            { EAs(e,f) } *)
 | LBRACE RBRACE                             { EDict([]) }
 | LBRACE fieldexps RBRACE                   { EDict($2) }
 | LT GT                                     { EArray(tyArrDefault,[]) }
 | LT es=exps GT                             { EArray(tyArrDefault,es) }
 | LT GT AS u=typ_term           { match u with
                                     | UArray(t) -> EArray(t,[])
                                     | _ -> printParseErr "bad array ann" }
 | LT es=exps GT AS u=typ_term   { match u with
                                     | UArray(t) -> EArray(t,es)
                                     | _ -> printParseErr "bad array ann" }

lambda : (* requiring parens around body to avoid conflicts *)
 | FUN p=pat ARROW LPAREN e=exp RPAREN         { mkFun p e }
 | FUN x=VAR xs=vars ARROW LPAREN e=exp RPAREN { mkCurriedFuns (x::xs) e }
     (* for mkCurriedFuns, match sequences of at least two variables to avoid
        conflicting with pat, which can match a single variable *)

typ :

 | LBRACE x=VAR PIPE p=formula RBRACE  { TRefinement(x,p) }
 | LBRACE p=formula RBRACE             { TRefinement("v",p) }

 | u=typ_term                          { tyTypTerm u }

 | REFTYPE LPAREN l=loc BANG RPAREN    { TNonNullRef l }
 | REFTYPE LPAREN l=loc QMARK RPAREN   { TMaybeNullRef (l, pTru) }

 | s=SUGAR                                         { mkSimpleSugarTyp s }
 | LBRACE s=SUGAR p=refinement                     { mkSugarTyp "v" s p }
 | LBRACE x=VAR COLON s=SUGAR p=refinement         { mkSugarTyp x s p }
 | qt=record_typ                                   { TQuick("v",qt,pTru) }
 | LBRACE qt=record_typ p=refinement               { TQuick("v",qt,p) }
 | LBRACE u=real_typ_term p=refinement             { TQuick("v",QBoxes[u],p) }
 | LBRACE x=VAR COLON u=real_typ_term p=refinement { TQuick(x,QBoxes[u],p) }

 | LT a=array_tuple_typs GT                        { tyArrayTuple a }

 (* {?(T)|p} is designed to help optimize calls to getIdx *)
 | LBRACE QMARK LPAREN t=typ RPAREN p=refinement   { TMaybeUndef(t,p) }

 (* [[x1:T1, x2:T2]] can be used in any type position... *)
 | LTUP RTUP                { TQuick("v",QTuple([],false),pTru) }
 | LTUP l=deptuple_ RTUP    { TQuick("v",QTuple(l,false),pTru) }

 (* ... but (x1:T1, x2:T2) can be used only as the domain of an arrow *)
deptuple :
 | LPAREN RPAREN              { [] }
 | LPAREN l=deptuple_ RPAREN  { l }

deptuple_ :
 | xot=varopttyp                   { [xot] }
 | xot=varopttyp COMMA l=deptuple_ { xot :: l }

refinement :
 | PIPE p=formula RBRACE { p }

record_typ :
 | LBRACE RBRACE { QRecd ([], false) }
 | LBRACE l=fieldtyps RBRACE
     { match List.rev l with
         | ("_",_)::rest -> QRecd (List.rev rest, true) 
         | _ -> if not (List.mem_assoc "_" l) then QRecd (l, false)
                else printParseErr "bad record type: _:Bot appears \
                       somewhere besides the last position" }

typ_term :
 | u=real_typ_term                       { u }
 | x=VAR                                 { UMacro(x) }

real_typ_term :
 | TVAR                                  { UVar($1) }
 | NULLBOX                               { UNull }
 | REFTYPE LPAREN l=loc RPAREN           { URef(l) }
 | ARRTYPE LPAREN t=typ RPAREN           { UArray(t) }
 | arr=arrow_typ                         { UArrow(arr) }

arrow_typ :
 | xt=arrow_dom ARROW t2=typ
     { expandHeapLocSugar (([],[],[]),fst xt,snd xt,emp,t2,emp) }

 | l=poly_formals xt=arrow_dom ARROW t2=typ
     { expandHeapLocSugar (l,fst xt,snd xt,emp,t2,emp) }

 | xt=arrow_dom DIV h1=dheap ARROW t2=typ DIV h2=rheap
     { popDHeap ();
       expandHeapLocSugar (([],[],[]),fst xt,snd xt,h1,t2,h2) }

 | l=poly_formals xt=arrow_dom DIV h1=dheap ARROW t2=typ DIV h2=rheap
     { popDHeap ();
       expandHeapLocSugar (l,fst xt,snd xt,h1,t2,h2) }

arrow_dom :
 | dt=deptuple         { (dummyBinder (), tyTupleSome dt) }
 | xt=vartyp_strict    { xt }

poly_formals :
 | LBRACK ts=tvars RBRACK                              { (ts,[],[]) }
 | LBRACK ts=tvars ls=semi_tvars RBRACK                { (ts,ls,[]) }
 | LBRACK ts=tvars ls=semi_tvars hs=semi_tvars RBRACK  { (ts,ls,hs) }
 | LBRACK SEMI ls=tvars hs=semi_tvars RBRACK           { ([],ls,hs) }
 | LBRACK SEMI ls=tvars RBRACK                         { ([],ls,[]) }
 | LBRACK SEMI SEMI hs=tvars RBRACK                    { ([],[],hs) }
 | LBRACK SEMI SEMI RBRACK                             { ([],[],[]) }

poly_actuals :
 | LBRACK ts=typs RBRACK                               { (ts,[],[]) }
 | LBRACK ts=typs ls=semi_locs RBRACK
 | LBRACK ts=typs ls=semi_locs SEMI RBRACK             { (ts,ls,[]) }
 | LBRACK SEMI ls=locs RBRACK                          { ([],ls,[]) }
 | LBRACK SEMI ls=locs SEMI RBRACK                     { ([],ls,[]) }
 | LBRACK SEMI SEMI RBRACK                             { ([],[],[]) }

formula :

 (***** simple predicates *****)
 | LPAREN EQ x=walue y=walue RPAREN                { PEq(x,y) }
 | LPAREN LT x=walue y=walue RPAREN                { lt x y }
 | LPAREN LE x=walue y=walue RPAREN                { le x y }
 | LPAREN GE x=walue y=walue RPAREN                { ge x y }
 | LPAREN GT x=walue y=walue RPAREN                { gt x y }

 (***** uninterpreted predicates *****)
 | LPAREN w=walue DCOLON u=typ_term RPAREN         { PHasTyp(w,u) }
 (* | LPAREN w=walue DCOLON u=typ_term BANG RPAREN    { pIsBang w u }  *)
 | LPAREN HEAPHAS h=hvar_ l=loc k=walue RPAREN     { PHeapHas(h,l,k) }
 | LPAREN PACKED w=walue RPAREN                    { packed w }
 | LPAREN INTEGER w=walue RPAREN                   { integer w }

 (***** logical connectives *****)
 | b=BOOL                                          { if b then pTru else pFls }
 | LPAREN OR ps=formulas RPAREN                    { pOr ps }
 | LPAREN AND ps=formulas RPAREN                   { pAnd ps }
 | LPAREN IMP p=formula q=formula RPAREN           { pImp p q }
 | LPAREN IFF p=formula q=formula RPAREN           { pIff p q }
 | LPAREN NOT p=formula RPAREN                     { pNot p }
 | LPAREN ITE p=formula q=formula r=formula RPAREN { pIte p q r }

 (***** delayed macros *****)
 | LPAREN HAS x=walue ys=walueset RPAREN           { PHas(x,ys) }
 | LPAREN HAS x=walue y=walue RPAREN               { PHas(x,[y]) }
 | HAS LPAREN x=walue COMMA y=walue RPAREN         { PHas(x,[y]) }
 | LPAREN DOM x=walue ys=walueset RPAREN           { PDomEq(x,ys) }
 | LPAREN EQMOD x=walue y=walue zs=walueset RPAREN { PEqMod(x,y,zs) }
 | LPAREN OBJHAS ds=waluelist k=walue h=hvar_ l=loc RPAREN { PObjHas(ds,k,h,l) }

 (***** syntactic macros *****)
 | LPAREN EQ x=walue ys=walueset RPAREN  { pOr (List.map (eq x) ys) }
 | LPAREN TRUTHY x=walue RPAREN          { pTruthy x }
 | LPAREN FALSY x=walue RPAREN           { pFalsy x }
 | LPAREN TYPE x=VAR RPAREN              { ParseUtils.doIntersectionHack x }
 | LPAREN t=typ w=walue RPAREN
     { match w with
         | WApp("sel",[k])   -> pAnd [has w k; applyTyp t w]
         | WHeapSel(h,l,k)   -> pAnd [PHeapHas(h,l,k); applyTyp t w]
         | WObjSel(ds,k,h,l) -> pAnd [PObjHas(ds,k,h,l); applyTyp t w]
         | _                 -> applyTyp t w }

formulas :
 | formula                               { [$1] }
 | formulas formula                      { $1 @ [$2] }

walue :
 | WBOT                                       { WBot }
 | v=value                                    { WVal v }
 | LPAREN TAG x=walue RPAREN                  { tag x }
 | LPAREN SEL x=walue y=walue RPAREN          { sel x y }
 | LPAREN PLUS x=walue y=walue RPAREN         { plus x y }
 | LPAREN MINUS x=walue y=walue RPAREN        { minus x y }
 | LPAREN UPD x=walue y=walue z=walue RPAREN  { upd x y z }
 | LPAREN LEN x=walue RPAREN                  { arrlen x }
 | LPAREN HEAPSEL h=hvar_ l=loc k=walue RPAREN             { WHeapSel(h,l,k) }
 | LPAREN OBJSEL ds=waluelist k=walue h=hvar_ l=loc RPAREN { WObjSel(ds,k,h,l) }

walueset :
 | LBRACE RBRACE                         { [] }
 | LBRACE walues RBRACE                  { $2 }

waluelist :
 | LBRACK RBRACK                         { [] }
 | LBRACK walues RBRACK                  { $2 }
 | w=walue                               { [w] }

dheap :
 | heap      { registerHeap $1 }

heap :
 | LPAREN RPAREN                                    { ([],[]) }
 | LPAREN l2=heapbindings RPAREN                    { ([],l2) }
 | h=TVAR PLUS LPAREN l2=heapbindings RPAREN        { ([h],l2) }
 | h=TVAR                                           { ([h],[]) }

rheap :
 | LPAREN RPAREN                                    { ([],[]) }
 | LPAREN l2=rheapbindings RPAREN                   { ([],l2) }
 | h=TVAR PLUS LPAREN l2=rheapbindings RPAREN       { ([h],l2) }
 (* | h=TVAR                                           { ([h],[]) }  *)
 (* parens for single heap variable in output heap to avoid conflict *)
 | LPAREN h=TVAR RPAREN                             { ([h],[]) }
 | SAME                                             { sameHeap true }
 | SAME_EXACT                                       { sameHeap true }
 | SAME_TYPE                                        { sameHeap false }

hvar_ :
 | h=TVAR                                           { ([h],[]) }
 | CUR                                              { ([curHeap],[]) }

frame :
 | LBRACK l=tvars RBRACK h1=dheap ARROW t2=typ DIV h2=rheap { (l,h1,(t2,h2)) }

ann :
 (* TODO change this sugar to insert temporary binding *)
 | DCOLON t=typ    { ParseUtils.typToFrame t }
 | TCOLON f=frame  { f }

pat :
 | VAR                       { PLeaf $1 }
 | LPAREN pats_ RPAREN       { PNode $2 }

pats_ :
 | pat                       { [$1] }
 | pat COMMA pats_           { $1 :: $3 }

loc_mapsto :
 | l=loc COLON  { l } (* l:        is preferred *)
 | l=loc MAPSTO { l } (* l |->     for legacy   *)

(* if i want to allow singleton types, better to map to a
   value directly (e.g. L |-> v or L |=> v) and add an HSing *)
(*
 | l=loc MAPSTO t=typ_                           { (l,HStrong(None,t,None)) }
 | l=loc MAPSTO LPAREN t=typ COMMA l2=loc RPAREN { (l,HStrong(None,t,Some(l2))) }
*)

heapbinding :
 | l=loc_mapsto x=thawstate            { (l,HWeak(x)) }
 | l=loc_mapsto xt=vartyp lo=proto_opt { let (x,t) = xt in
                                         (l,HStrong(Some(x),t,lo,None)) }

 (* NOTE: these should only be used in input heaps *)
 (* l: x:T [S] > l'         *)
 (* l: x:T [sameType] > l'  *)
 (* l: x:T [sameExact] > l' *)
 | l=loc_mapsto xt=vartyp LBRACK s=typ RBRACK lo=proto_opt
     { let (x,t) = xt in (l,HStrong(Some(x),t,lo,Some(s))) }
 | l=loc_mapsto xt=vartyp LBRACK SAME_TYPE RBRACK lo=proto_opt
     { let (x,t) = xt in (l,HStrong(Some(x),t,lo,Some(t))) }
 | l=loc_mapsto xt=vartyp LBRACK SAME_EXACT RBRACK lo=proto_opt
     { let (x,t) = xt in (l,HStrong(Some(x),t,lo,Some(valToSingleton (vVar x)))) }

proto_opt :
 |          { None   }
 | GT l=loc { Some l }

rheapbinding :
 | heapbinding              { $1 }
 | l=loc_mapsto SAME        { (l, sameCell true l) }
 | l=loc_mapsto SAME_EXACT  { (l, sameCell true l) }
 | l=loc_mapsto SAME_TYPE   { (l, sameCell false l) }

heapenvbinding :
 | l=loc_mapsto x=thawstate                     { (l,HEWeak(x)) }
 | l=loc_mapsto v=value lo=proto_opt            { (l,HEStrong(v,lo,None)) }
 | l=loc_mapsto v=value lo=proto_opt ci=typ_opt { (l,HEStrong(v,lo,ci)) }

weakloc : LPAREN wl=weakloc_ RPAREN { wl }

weakloc_ : m=loc_mapsto t=typ GT l=loc { (m,t,l) }

loc :
 | x=TVAR       { LocVar(x) }
 | x=VAR        { LocConst(x) }

thawstate :
 | FRZN         { Frzn }
 | THWD l=loc   { Thwd(l) }

varopt :
 | x=VAR                    { x }
 | UNDERSCORE               { dummyBinder() }

varopttyp :
 | x=VAR COLON t=sugar_typ       { (Some x, t) }
 | UNDERSCORE COLON t=sugar_typ  { (None, t) }
 | t=sugar_typ                   { (None, t) }

sugar_typ :
 | t=typ                         { t }
 | REFTYPE                       { tyAnonRef }
 | REFTYPE QMARK                 { tyAnonMaybeRef }

vartyp :
 | xt=vartyp_strict         { xt }
 | t=typ                    { (dummyBinder (), t) }

vartyp_strict :
 | x=VAR COLON t=typ        { (x, t) }
 | UNDERSCORE COLON t=typ   { (dummyBinder (), t) }
 
typ_opt :
 | UNDERSCORE               { None }
 | t=typ                    { Some t }


(***** lists of things ********************************************************)

vars :
 | VAR                 { [$1] }
 | VAR vars            { $1 :: $2 }

locs :
 | loc                 { [$1] }
 | loc COMMA locs      { $1 :: $3 }

tvars :
 | TVAR                { [$1] }
 | TVAR COMMA tvars    { $1 :: $3 }

semi_locs:
 | SEMI                { [] }
 | SEMI ls=locs        { ls }

semi_tvars:
 | SEMI                { [] }
 | SEMI ts=tvars       { ts }

exps :
 | exp                 { [$1] }
 | exp COMMA exps      { $1 :: $3 }

typs :
 | typ                 { [$1] }
 | typ COMMA typs      { $1 :: $3 }

fieldexp :
 | e1=exp EQ e2=exp          { (e1,e2) }

fieldexps : (* weird: combining the field and fields leads to type error... *)
 | fieldexp                  { [$1] }
 | fieldexp SEMI fieldexps   { $1 :: $3 }
 | fieldexp COMMA fieldexps  { $1 :: $3 }

fieldtyp :
 | f=STR COLON t=typ         { (f,t) }
 | f=VAR COLON t=typ         { (f,t) }
 (* as a quick fix to avoid conflicts, putting _:Bot here and then
    checking for it in record_typ *)
 | UNDERSCORE COLON BOT      { ("_",tyAny) }

fieldtyps :
 | fieldtyp                  { [$1] }
 | fieldtyp COMMA fieldtyps  { $1 :: $3 }

walues :
 | walue                 { [$1] }
 | walue COMMA walues    { $1 :: $3 }

array_tuple_typs :
 | att=array_tuple_typs_  { let (ts,b) = att in
                            let tInvariant = tyNotUndef in
                            (tInvariant,ts,b) }

array_tuple_typs_ :
 | t=typ                             { ([t],false) }
 | t=typ COMMA ELLIPSIS              { ([t],true) }
 | t=typ COMMA att=array_tuple_typs_ { let (ts,b) = att in (t::ts,b) }

heapbindings :
 | heapbinding                     { [$1] }
 | heapbinding COMMA heapbindings  { $1 :: $3 }

rheapbindings :
 | rheapbinding                      { [$1] }
 | rheapbinding COMMA rheapbindings  { $1 :: $3 }

heapenvbindings :
 | heapenvbinding                        { [$1] }
 | heapenvbinding COMMA heapenvbindings  { $1 :: $3 }

(*
heaps :
 | heap                  { [$1] }
 | heap COMMA heaps      { $1 :: $3 }
*)


(***** DjsDesugar entry points ************************************************)

(* including even trivial wrapper productions so that EOF can ensure the
   entire string annotation is parsed *)

jsTyp : t=typ EOF { t }

jsPolyArgs : l=poly_actuals EOF { l }

jsFail : FAIL s=STR EOF { s } 

jsWhile :
 | h1=dheap ARROW h2=rheap
     { match h1, h2 with
         | ([],cs1), ([],cs2) ->
             let h = freshHVar () in
             ([h], ([h],cs1), (tyAny,([h],cs2)))
         | _ ->
             printParseErr "bad jsWhile format" }
 | LBRACK h=TVAR RBRACK h1=dheap ARROW h2=rheap
     { match h1, h2 with
         | ([x],cs1), ([y],cs2) when x = h && y = h ->
             ([h], ([h],cs1), (tyAny,([h],cs2)))
         | _ ->
             printParseErr "bad jsWhile format" }

jsLoc : l=loc EOF { l }

jsWeakLoc : w=weakloc EOF { w }

jsFreeze : x=VAR LPAREN l=loc COMMA ts=thawstate RPAREN { (x, l, ts) }

jsThaw : x=VAR l=loc { (x, l) }

jsObjLocs :
 | l=loc EOF                             { (l, None) }
 | l=loc l2=loc EOF                      { (l, Some l2) }
 (* | LPAREN l=loc COMMA l2=loc RPAREN EOF  { (l, Some l2) } *)

jsCtor:
 | NEW arr=arrow_typ EOF
 | arr=arrow_typ EOF      { UArrow(arr) }
 | NEW x=VAR EOF
 | x=VAR EOF              { UMacro(x) }

jsNew :
 | lNew=loc EOF                               { (lNew,None,None) }
 | lNew=loc GT lProto=loc EOF                 { (lNew,Some(lProto),None) }
 | lNew=loc GT lProto=loc l=poly_actuals EOF  { (lNew,Some(lProto),Some(l)) }
 | lNew=loc l=poly_actuals EOF                { (lNew,None,Some(l)) }

jsArrLit :
 | l=loc EOF                             { (l, tyArrDefault) }
 | l=loc ARRTYPE LPAREN t=typ RPAREN EOF { (l, t) }
 | ARRTYPE LPAREN t=typ RPAREN EOF       { (LocConst (freshVar "arrLit"), t) }
 | l=loc LT a=array_tuple_typs GT EOF    { (l, tyArrayTuple a) }

jsHeap : h=heap EOF { h }

jsMacroDef :
 | TYPE x=VAR EQ t=typ EOF            { x,MacroT(t) }
 | TYPE x=VAR DCOLON tt=typ_term EOF  { x,MacroTT(tt) }

%%
