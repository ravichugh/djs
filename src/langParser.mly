%{

(* ocamlbuilding with -use-menhir flag. differences with ocamlyacc:
    - ocaml comments everywhere
    - multiple patterns for a single action
    - LangParser.Error instead of Parsing.Parse_error
    - the $startpos,$endpos syntax

   lots of refactorings can be done:
    - use built in lists and options
    - parametrize grammar with different dep tuple syntax
*)


open Lang
open LangUtils
open Settings


(* shadowing failwith, since Failure is getting caught when parsing
   with menhir. use parse_err instead. *)
let failwith = 0

(* let parse_err s = raise (Lang.Parse_error s) *)
let printParseErr = Log.printParseErr

let eOp1 (s,x)     = mkApp (eVar s) [x]
let eOp2 (s,x,y)   = mkApp (eVar s) [x;y]
let eOp3 (s,x,y,z) = mkApp (eVar s) [x;y;z]

(* make curried lambdas, putting polyFormals on the first lambda *)
let mkCurriedFuns xs e =
  let rec foo = function
    | []    -> printParseErr "mkCurriedFuns: need at least one value var"
    | x::[] -> EFun (PLeaf x, e)
    | x::xs -> EFun (PLeaf x, foo xs)
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

(*
let addHeapPrefixVar ts ls x t cs1 t2 cs2 =
  let h = freshHVar () in
  ((ts,ls,[h]), x, t, ([h],cs1), t2, ([h],cs2))
*)

let emp = ([],[])

let mkSugarTyp x s p =
  match s with (* NOTE: keep these in sync with LangUtils.simpleSugarToTyp *)
    | "Int"  -> TQuick(x,QBase(BInt),p)
    | "Num"  -> TQuick(x,QBase(BNum),p)
    | "Bool" -> TQuick(x,QBase(BBool),p)
    | "Str"  -> TQuick(x,QBase(BStr),p)
    | "Dict" -> TRefinement(x,pAnd[pDict;p])
    | _      -> printParseErr (spr "bad sugar {%s:%s|%s}" x s (strForm p))


(***** Stuff for System !D ****************************************************)

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
  if exact then ty (PEq (theV, wVar x)) else s

(* 8/14/12: could try to avoid unnecessary binders when using same* tokens *)

let freshenCell exact = function
  | HConc(None,s) -> printParseErr "freshenCell"
  | HConcObj(None,s,l') -> printParseErr "freshenCell"
  | HConc(Some(x),s) -> HConc (Some (freshVar x), copyCell exact x s)
  | HConcObj(Some(x),s,l') -> HConcObj (Some (freshVar x), copyCell exact x s, l')
  | HWeakTok(tok) -> HWeakTok tok

let sameHeap exact =
  let (hs,cs) = List.hd !heapStack in
  let cs = List.map (fun (l,hc) -> (l, freshenCell exact hc)) cs in
  (hs, cs)

let sameCell exact l =
  try freshenCell exact (List.assoc l (snd (List.hd !heapStack)))
  with
    Not_found ->
    printParseErr (spr "sameCell: [%s] not found in previous heap" (strLoc l))
  | Failure("hd") ->
    printParseErr "sameCell: empty heap"

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
  EOF TAG (* TRUE FALSE *) LET REC EQ IN FUN ARROW IF THEN ELSE
  LPAREN RPAREN LBRACE RBRACE LBRACK RBRACK (* ALL *) DOT COMMA
  SEMI DCOLON COLON AS GT (* GTGT *) EXTERN FAIL (* VTRUE VFALSE *) PIPE
  OR IMP IFF NOT AND ITE HAS SEL UPD EQMOD DOM WBOT EMPTY
  TYPE NULL NULLBOX NEW (* LIST *) BANG QMARK
(*
  SUGAR_INT SUGAR_BOOL SUGAR_TOP SUGAR_DICT SUGAR_BOT
  SUGAR_INTORBOOL SUGAR_STR SUGAR_INTORSTR SUGAR_STRORBOOL SUGAR_NUM
  SUGAR_NUMORBOOL SUGAR_EMPTY
  SUGAR_EXTEND SUGAR_FLD SUGAR_UNDEF SUGAR_NOTUNDEF
*)
  PLUS MINUS MUL DIV LT LE GE (* NE EQEQ AMPAMP PIPEPIPE *) PLUSPLUS
  ASSGN (* LOCALL *) NEWREF REFTYPE (* AT *) MAPSTO SAME HEAP
  SAME_TYPE SAME_EXACT
  FRZN THWD FREEZE THAW (* REFREEZE *)
  ARRTYPE PACKED LEN TRUTHY FALSY INTEGER
  BREAK THROW TRY CATCH FINALLY
  UNDEF
  UNDERSCORE TCOLON ELLIPSIS
  HEAPHAS HEAPSEL OBJHAS OBJSEL
  WITH BEGIN END
  LTUP RTUP


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
%type <Lang.uarrow> jsCtor
%type <(Lang.typs * Lang.locs * Lang.heaps) * Lang.loc> jsNew
%type <Lang.loc * Lang.typ> jsArrLit
%type <Lang.heap> jsHeap
%type <string> jsFail


%start prog prelude
%start jsTyp jsPolyArgs jsLoc jsObjLocs jsWhile jsFail jsCtor jsNew jsArrLit
       jsHeap jsFreeze jsThaw jsWeakLoc


%%

prog : exp EOF     { $1 }

prelude :
 | EOF                                 { fun e -> e }
 | EXTERN x=VAR DCOLON t=typ p=prelude { fun e -> EExtern(x,t,p(e)) }
 | LET x=VAR a=ann EQ e0=exp p=prelude { fun e -> ELet(x,Some(a),e0,p(e)) }
 | LET x=VAR EQ e0=exp p=prelude       { fun e -> ELet(x,None,e0,p(e)) }

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
 (* quick hack: using begin/end to avoid conflicts *)
 | BEGIN e=lambda END
     { match Anf.coerce e with (* no grammar for ANF exps, so coerce *)
         | EVal(v) -> v.value
         | _ -> printParseErr "coerce lambda"}

value :
 | v=value_ { { pos=pos0; value=v } }

exp :
 | exp1                                   { $1 }
 | IF exp THEN exp ELSE exp               { EIf($2,$4,$6) }
 | LET x=varopt EQ e1=exp IN e2=exp       { ELet(x,None,e1,e2) }
 | LET x=varopt a=ann EQ e1=exp IN e2=exp { ELet(x,Some(a),e1,e2) }
 (* | LET REC VAR DCOLON scm EQ exp IN exp  { ParseUtils.mkLetRec $3 $5 $7 $9 } *)
 | EXTERN VAR DCOLON typ exp             { EExtern($2,$4,$5) }
 | HEAP w=weakloc e=exp                  { EWeak(w,e) }
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
 | e1=exp1 e2=exp2               { EApp(([],[],[]),e1,e2) }
 | LPAREN l=poly_actuals e1=exp1 RPAREN e2=exp2 { EApp(l,e1,e2) }
 | BANG e=exp2                   { EDeref(e) }
 | e1=exp1 ASSGN e2=exp2         { ESetref(e1,e2) }
 | NEWREF l=loc e=exp2
     { match l with
         | LocConst(x) when x.[0] = '&' -> ENewref(l,e)
         | _ -> printParseErr (spr "ref %s isn't an & address" (strLoc l)) }
 | NEW LPAREN e1=exp COMMA l1=loc COMMA e2=exp COMMA l2=loc RPAREN
     { ENewObj(e1,l1,e2,l2) }
 | FREEZE LPAREN l=loc COMMA x=thawstate COMMA e=exp RPAREN
     { EFreeze(l,x,e) }
 | THAW LPAREN l=loc COMMA e=exp RPAREN      { EThaw(l,e) }

exp2 :
 | v=value                                   { EVal v }
 | e=lambda                                  { e }
 | LPAREN exp RPAREN                         { $2 }
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

 | LBRACE x=VAR PIPE p=formula RBRACE     { TRefinement(x,p) }
 | LBRACE p=formula RBRACE                { TRefinement("v",p) }
 | u=typ_term                             { tyTypTerm u }

 | s=SUGAR  { if List.mem_assoc s LangUtils.simpleSugarToTyp
              then List.assoc s LangUtils.simpleSugarToTyp
              else printParseErr (spr "unexpected Sugar: [%s]" s) }

 | LBRACE s=SUGAR             PIPE p=formula RBRACE { mkSugarTyp "v" s p }
 | LBRACE x=VAR COLON s=SUGAR PIPE p=formula RBRACE { mkSugarTyp x s p }
 | LBRACE u=typ_term          PIPE p=formula RBRACE { TQuick("v",QBoxes[u],p) }

 (* parens to avoid conflicts *)
 | LPAREN t=typ RPAREN BANG               { TNonNull(t) }
 | LPAREN t=typ RPAREN QMARK              { TMaybeNull(t) }

 (* be careful of conflicts *)
 | l=deptuple_some                        { TQuick("v",QTuple(l,false),pTru) }

 | LT x=array_tuple_typs GT { let (ts,tInv,b) = x in tyArrayTuple tInv ts b }

deptuple_some :
 (* using square brackets so vartyp and deptuple don't conflict in arr_dom *) 
 | LBRACK RBRACK                         { [] }
 | LBRACK l=deptuple_somebinders RBRACK  { l }

deptuple_somebinders :
 | xot=varopttyp                              { [xot] }
 | xot=varopttyp COMMA l=deptuple_somebinders { xot :: l }

deptuple_allbinders :
 | xt=vartyp                                  { [xt] }
 | xt=vartyp COMMA l=deptuple_allbinders      { xt :: l }

typ_term :
 | TVAR                                  { UVar($1) }
 | NULLBOX                               { UNull }
 | REFTYPE LPAREN l=loc RPAREN           { URef(l) }
 | u=arrow_typ                           { u }
 | ARRTYPE LPAREN t=typ RPAREN           { UArray(t) }

arrow_typ :

 | xt=arrow_dom ARROW t2=typ
     { UArrow (ParseUtils.maybeAddHeapPrefixVar
                 (([],[],[]),fst xt,snd xt,emp,t2,emp)) }

 | l=poly_formals xt=arrow_dom ARROW t2=typ
     { UArrow (ParseUtils.maybeAddHeapPrefixVar
                 (l,fst xt,snd xt,emp,t2,emp)) }

 | xt=arrow_dom DIV h1=dheap ARROW t2=typ DIV h2=rheap
     { popDHeap ();
       UArrow (ParseUtils.maybeAddHeapPrefixVar
                 (([],[],[]),fst xt,snd xt,h1,t2,h2)) }

 | l=poly_formals xt=arrow_dom DIV h1=dheap ARROW t2=typ DIV h2=rheap
     { popDHeap ();
       UArrow (ParseUtils.maybeAddHeapPrefixVar
                 (l,fst xt,snd xt,h1,t2,h2)) }

(*

(* NOTE: the limitations here in the parser need to be taken into account
   when printing arrows (LangUtils.strTT) *)

*)
arrow_dom :
 | LPAREN xt=vartyp RPAREN  { (fst xt, snd xt) }
 | xt=vartyp                { (fst xt, snd xt) }
(* TODO
 | dt=deptuple              { (dummyBinder (), tyTupleSome dt) }
*)

(* TODO clearly a better way to organize poly_formals and poly_actuals ... *)

poly_formals :
 | LBRACK ts=tvars RBRACK
 | LBRACK ts=tvars SEMI RBRACK
 | LBRACK ts=tvars SEMI SEMI RBRACK             { (ts,[],[]) }
 | LBRACK ts=tvars SEMI ls=tvars RBRACK
 | LBRACK ts=tvars SEMI ls=tvars SEMI RBRACK    { (ts,ls,[]) }
 | LBRACK SEMI ls=tvars RBRACK
 | LBRACK SEMI ls=tvars SEMI RBRACK             { ([],ls,[]) }
 | LBRACK SEMI ls=tvars SEMI hs=tvars RBRACK    { ([],ls,hs) }
 | LBRACK SEMI SEMI hs=tvars RBRACK             { ([],[],hs) }
 | LBRACK ts=tvars SEMI SEMI hs=tvars RBRACK    { (ts,[],hs) }
 | LBRACK SEMI SEMI RBRACK                      { ([],[],[]) }
 | LBRACK ts=tvars SEMI ls=tvars SEMI hs=tvars RBRACK { (ts,ls,hs) }

poly_actuals :
 | LBRACK ts=typs RBRACK
 | LBRACK ts=typs SEMI RBRACK
 | LBRACK ts=typs SEMI SEMI RBRACK              { (ts,[],[]) }
 | LBRACK ts=typs SEMI ls=locs RBRACK           { (ts,ls,[]) }
 | LBRACK ts=typs SEMI ls=locs SEMI RBRACK      { (ts,ls,[]) }
 | LBRACK SEMI SEMI RBRACK                      { ([],[],[]) }
 | LBRACK SEMI SEMI hs=heaps RBRACK             { ([],[],hs) }
 | LBRACK SEMI ls=locs SEMI hs=heaps RBRACK     { ([],ls,hs) }
 | LBRACK SEMI ls=locs RBRACK
 | LBRACK SEMI ls=locs SEMI RBRACK              { ([],ls,[]) }

formula :
 (***** simple predicates *****)
 | LPAREN EQ x=walue y=walue RPAREN             { PEq(x,y) }
 | LPAREN LT x=walue y=walue RPAREN             { lt x y }
 | LPAREN LE x=walue y=walue RPAREN             { le x y }
 | LPAREN GE x=walue y=walue RPAREN             { ge x y }
 | LPAREN GT x=walue y=walue RPAREN             { gt x y }
 (***** uninterpreted predicates *****)
 | LPAREN w=walue DCOLON u=typ_term RPAREN      { PHasTyp(w,u) }
 | LPAREN w=walue DCOLON u=typ_term BANG RPAREN { pIsBang w u }
(*
 | HEAPHAS LPAREN h=heap COMMA l=loc COMMA k=walue RPAREN { PHeapHas(h,l,k) }
*)
 | LPAREN HEAPHAS h=heap l=loc k=walue RPAREN   { PHeapHas(h,l,k) }
 | LPAREN PACKED w=walue RPAREN                 { packed w }
 | LPAREN INTEGER w=walue RPAREN                { integer w }
 (***** logical connectives *****)
 | b=BOOL                                       { if b then pTru else pFls }
 | LPAREN OR ps=formulas RPAREN                 { pOr ps }
 | LPAREN AND ps=formulas RPAREN                { pAnd ps }
 | LPAREN IMP p=formula q=formula RPAREN        { pImp p q }
 | LPAREN IFF p=formula q=formula RPAREN        { pIff p q }
 | LPAREN NOT p=formula RPAREN                  { pNot p }
 | LPAREN ITE p=formula q=formula r=formula RPAREN { pIte p q r }
 (***** delayed macros *****)
 | LPAREN HAS x=walue ys=walueset RPAREN        { PHas(x,ys) }
 | LPAREN HAS x=walue y=walue RPAREN            { PHas(x,[y]) }
 | HAS LPAREN x=walue COMMA y=walue RPAREN      { PHas(x,[y]) }
 | LPAREN DOM x=walue ys=walueset RPAREN        { PDomEq(x,ys) }
 | LPAREN EQMOD x=walue y=walue zs=walueset RPAREN { PEqMod(x,y,zs) }
 (***** syntactic macros *****)
 (* TODO rethink these wrt quick types *)
 | LPAREN w=walue TCOLON t=typ RPAREN           { applyTyp t w }
 | LPAREN w=walue COLON t=typ RPAREN            { applyTyp t w }
(*
 | OBJHAS LPAREN d=walue COMMA k=walue COMMA h=heap COMMA l=loc RPAREN
     { PObjHas([d],k,h,l) }
 | OBJHAS LPAREN ds=waluelist COMMA k=walue COMMA h=heap COMMA l=loc RPAREN
     { PObjHas(ds,k,h,l) }
*)
 | LPAREN OBJHAS d=walue k=walue h=heap l=loc RPAREN      { PObjHas([d],k,h,l) }
 | LPAREN OBJHAS ds=waluelist k=walue h=heap l=loc RPAREN { PObjHas(ds,k,h,l) }
 | LPAREN TYPE x=VAR RPAREN  { ParseUtils.doIntersectionHack x }

(*
 | LPAREN SUGAR_EXTEND a1=atom a2=atom a3=atom a4=atom RPAREN
     { pExtend a1 a2 a3 a4 }

 | LPAREN SUGAR_FLD a1=atom a2=atom t=typ RPAREN
     { let TRefinement(x,p) = t in
       PAnd [PEq (tag a2, aStr "Str"); (* TODO better not to hardcode Str *)
             PEq (has a1 a2, ATru);
             substForm (sel a1 a2) (aVar x) p] }
*)

 (* TODO probably want to add PTruthy and PFalsy as delayed macros *)
 | LPAREN TRUTHY x=walue RPAREN                 { pTruthy x }
 | LPAREN FALSY x=walue RPAREN                  { pFalsy x }

 | LPAREN OBJSEL ds=waluelist k=walue h=heap l=loc COLON t=typ RPAREN
     { pAnd [PObjHas(ds,k,h,l); applyTyp t (WObjSel(ds,k,h,l))] }

formulas :
 | formula                               { [$1] }
 | formulas formula                      { $1 @ [$2] }

walue :
 | WBOT                                      { WBot }
 | v=value                                   { WVal v }
 | LPAREN TAG x=walue RPAREN                 { tag x }
 | TAG LPAREN x=walue RPAREN                 { tag x }
 | LPAREN SEL x=walue y=walue RPAREN         { sel x y }
 | LPAREN PLUS x=walue y=walue RPAREN        { plus x y }
 | LPAREN MINUS x=walue y=walue RPAREN       { minus x y }
 | LPAREN UPD x=walue y=walue z=walue RPAREN { upd x y z }
 | LPAREN LEN x=walue RPAREN                 { arrlen x }
(*
 | HEAPSEL LPAREN h=heap COMMA l=loc COMMA k=walue RPAREN
     { WHeapSel(h,l,k) }
 | OBJSEL LPAREN d=walue COMMA k=walue COMMA h=heap COMMA l=loc RPAREN
     { WObjSel([d],k,h,l) }
 | OBJSEL LPAREN ds=waluelist COMMA k=walue COMMA h=heap COMMA l=loc RPAREN
     { WObjSel(ds,k,h,l) }
*)
 | LPAREN HEAPSEL h=heap l=loc k=walue RPAREN             { WHeapSel(h,l,k) }
 | LPAREN OBJSEL d=walue k=walue h=heap l=loc RPAREN      { WObjSel([d],k,h,l) }
 | LPAREN OBJSEL ds=waluelist k=walue h=heap l=loc RPAREN { WObjSel(ds,k,h,l) }

walueset :
 | LBRACE RBRACE                         { [] }
 | LBRACE walues RBRACE                  { $2 }

waluelist :
 | LBRACK RBRACK                         { [] }
 | LBRACK walues RBRACK                  { $2 }

dheap :
 | heap      { registerHeap $1 }

heap :
 | LBRACK RBRACK                                 { ([],[]) }
 | LBRACK l2=heapcells RBRACK                    { ([],l2) }
 | LBRACK l1=tvars RBRACK                        { (l1,[]) }
 | LBRACK l1=tvars PLUSPLUS l2=heapcells RBRACK  { (l1,l2) }
 | h=TVAR                                        { ([h],[]) }
 (* TODO generalize to multiple weaklocs *)
 | LBRACK wl=weakloc_ PLUSPLUS hcl=heapcells RBRACK
     { Log.printParseErr "need arrows to abstract over weak heaps" }

rheap :
 | LBRACK RBRACK                                 { ([],[]) }
 | LBRACK l2=rheapcells RBRACK                   { ([],l2) }
 | LBRACK l1=tvars RBRACK                        { (l1,[]) }
 | LBRACK l1=tvars PLUSPLUS l2=rheapcells RBRACK { (l1,l2) }
 | h=TVAR                                        { ([h],[]) }
 | SAME                                          { sameHeap true }
 | SAME_EXACT                                    { sameHeap true }
 | SAME_TYPE                                     { sameHeap false }

frame :
 | LBRACK l=tvars RBRACK h1=dheap ARROW t2=typ DIV h2=rheap { (l,h1,(t2,h2)) }

ann :
 (* TODO change this sugar to insert temporary binding *)
 | DCOLON t=typ    { ParseUtils.typToFrame t }
 | TCOLON f=frame  { f }

fieldexp :
 | e1=exp EQ e2=exp    { (e1,e2) }

(*
fieldtyp :
 | STR COLON typ             { ($1,$3) }
*)

pat :
 | VAR                       { PLeaf $1 }
 | LPAREN pats_ RPAREN       { PNode $2 }

pats_ :
 | pat                       { [$1] }
 | pat COMMA pats_           { $1 :: $3 }

heapcell :
 | l=loc MAPSTO x=varopt COLON t=typ { (l, HConc (Some x,t)) }
 | l=loc MAPSTO LPAREN x=varopt COLON t=typ COMMA l2=loc RPAREN
     { (l, HConcObj (Some x,t,l2)) }
(*
 | l=loc MAPSTO LPAREN x=thawstate COMMA t=typ COMMA l2=loc RPAREN
     { (l,HWeakObj(x,t,l2)) }
*)
 | l=loc MAPSTO x=thawstate { (l,HWeakTok(x)) }

rheapcell :
 | heapcell                 { $1 }
 | l=loc MAPSTO SAME        { (l, sameCell true l) }
 | l=loc MAPSTO SAME_EXACT  { (l, sameCell true l) }
 | l=loc MAPSTO SAME_TYPE   { (l, sameCell false l) }
 (* TODO add weak obj *)

weakloc :
 | LBRACK wl=weakloc_ RBRACK { wl }

weakloc_ :
 | m=loc MAPSTO LPAREN t=typ COMMA l=loc RPAREN { (m,t,l) }

thawstate :
 | FRZN       { Frzn }
 | THWD l=loc { Thwd(l) }

varopt :
 | x=VAR                { x }
 | UNDERSCORE           { dummyBinder() }

varopttyp :
 | x=VAR COLON t=typ      { (Some x, t) }
 | UNDERSCORE COLON t=typ { (None, t) }
 
vartyp :
 | x=varopt COLON t=typ             { (x,t) }
 | LTUP RTUP                        { (dummyBinder (), tyTupleAll []) }
 | LTUP dt=deptuple_allbinders RTUP { (dummyBinder (), tyTupleAll dt) }
(*
 | dt=deptuple          { (dummyBinder (), TTuple dt) }
*)
(* TODO this would add lots of conflicts, but really want a way to
     allow this, especially when the arg is a deptuple
 | t=typ                { (dummyBinder(),t) }
*)

loc :
 | x=TVAR               { LocVar(x) }
 | x=VAR                { LocConst(x) }


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

(*
lvars :
 | LVAR                { [$1] }
 | LVAR COMMA lvars    { $1 :: $3 }

hvars :
 | HVAR                { [$1] }
 | HVAR COMMA hvars    { $1 :: $3 }
*)

exps :
 | exp                 { [$1] }
 | exp COMMA exps      { $1 :: $3 }

typs :
 | typ                 { [$1] }
 | typ COMMA typs      { $1 :: $3 }

fieldexps : (* weird: combining the field and fields leads to type error... *)
 | fieldexp                  { [$1] }
 | fieldexp SEMI fieldexps   { $1 :: $3 }

walues :
 | walue                 { [$1] }
 | walue COMMA walues    { $1 :: $3 }

array_tuple_typs :
 | att=array_tuple_typs_
     { let (ts,b) = att in
(* 3/14
       (* instead of using not (v = undefined), taking the join
          of all the components. assuming the binder of each component
          is "v". *)

       no, this is not a good idea until EArray/VArray keep the invariant
       and other predicates separate, so that they can each be omitted/supplied
       independently.

       let tInvariant =
         match Utils.removeDupes ts with
           | []  -> tyNotUndef
           | [t] -> t
           | ts' -> ty (pOr (List.map (fun t -> applyTyp t theV) ts'))
       in
*)
       let tInvariant = tyNotUndef in
       (ts,tInvariant,b) }

array_tuple_typs_ :
 | t=typ                             { ([t],false) }
 | t=typ COMMA ELLIPSIS              { ([t],true) }
 | t=typ COMMA att=array_tuple_typs_ { let (ts,b) = att in (t::ts,b) }

(*
fieldtyps :
 | fieldtyp                  { [$1] }
 | fieldtyp SEMI fieldtyps   { $1 :: $3 }
*)

(*
typs_mul :
 | typ                       { [$1] }
 | typ MUL typs_mul          { $1 :: $3 }
*)

heapcells :
 | heapcell                  { [$1] }
 | heapcell COMMA heapcells  { $1 :: $3 }

rheapcells :
 | rheapcell                   { [$1] }
 | rheapcell COMMA rheapcells  { $1 :: $3 }

heaps :
 | heap                  { [$1] }
 | heap COMMA heaps      { $1 :: $3 }


(***** DjsDesugar entry points ************************************************)

(* including even trivial wrapper productions so that EOF can ensure the
   entire string annotation is parsed *)

jsTyp : t=typ EOF { t }

jsPolyArgs : l=poly_actuals EOF { l }

jsFail : FAIL s=STR EOF { s } 

jsWhile :
 | f=frame EOF  { f }
 | t=typ EOF    { ParseUtils.typToFrame t }
 | h1=dheap ARROW h2=rheap
     { match h1, h2 with
         | ([],cs1), ([],cs2) ->
             let h = freshHVar () in
             ([h], ([h],cs1), (tyAny,([h],cs2)))
         | _ -> printParseErr "bad jsWhile format" }

jsLoc : l=loc EOF { l }

jsWeakLoc : w=weakloc EOF { w }

jsFreeze : x=VAR LPAREN l=loc COMMA ts=thawstate RPAREN { (x, l, ts) }

jsThaw : x=VAR l=loc { (x, l) }

jsObjLocs :
 | l=loc EOF                             { (l, None) }
 | l=loc l2=loc EOF                      { (l, Some l2) }
 (* | LPAREN l=loc COMMA l2=loc RPAREN EOF  { (l, Some l2) } *)

jsCtor: NEW u=arrow_typ EOF { match u with
                                | UArrow(arr) -> arr
                                | _ -> printParseErr "jsCtor: impossible"  }

jsNew : x=poly_actuals y=loc EOF  { (x,y) }

jsArrLit :
 | l=loc EOF                             { (l, tyArrDefault) }
 | l=loc ARRTYPE LPAREN t=typ RPAREN EOF { (l, t) }
 | ARRTYPE LPAREN t=typ RPAREN EOF       { (LocConst (freshVar "arrLit"), t) }
 | l=loc LT x=array_tuple_typs GT EOF
     { let (ts,tInvariant,b) = x in (l, tyArrayTuple tInvariant ts b) }
(*
 | l=loc EOF        { (l, tyArrDefault) }
 | l=loc t=typ EOF  { (l, t) }
 | t=typ EOF        { (LocConst (freshVar "arrLit"), t) }
 | l=loc LT x=array_tuple_typs GT EOF
     { let (ts,tInvariant,b) = x in (l, tyArrayTuple tInvariant ts b) }
*)

jsHeap : h=heap EOF { h }

%%
