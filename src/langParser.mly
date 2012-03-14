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

let parse_err s = raise (Lang.Parse_error s)

let eOp1 (s,x)     = mkApp (eVar s) [x]
let eOp2 (s,x,y)   = mkApp (eVar s) [x;y]
let eOp3 (s,x,y,z) = mkApp (eVar s) [x;y;z]

(* make curried lambdas, putting polyFormals on the first lambda *)
let mkCurriedFuns polyFormals xs e =
  let rec foo l = function
    | []    -> parse_err "mkCurriedFuns: need at least one value var"
    | x::[] -> EFun (l, x, None, e)
    | x::xs -> EFun (l, x, None, foo ([],[],[]) xs)
  in foo polyFormals xs

let mkFun polyFormals p e =
  match p with
    | PLeaf(x) -> mkCurriedFuns polyFormals [x] e
    | _        -> ParseUtils.mkPatFun polyFormals p e

(* not using LangUtils.freshVar, since want a version that does not
   insert leading zeroes and does not keep a counter across all freshvars *)
let dummyBinder =
  let c = ref 0 in
  fun () ->
    incr c;
    spr "%s_%d" "_dummy" !c

(*
let addHeapPrefixVar ts ls x t cs1 t2 cs2 =
  let h = freshHVar () in
  ((ts,ls,[h]), x, t, ([h],cs1), t2, ([h],cs2))
*)

let emp = ([],[])


(***** Stuff for System !D ****************************************************)

let heapStack : heap list ref = ref []
(* every time a heap is parsed inside a type, push it onto this stack.
   this is used to help expand occurrences of "same" during parsing.
   since every heap is pushed onto this stack, pop two heaps after an
   impure arrow is successfully parsed. *)

let registerHeap h =
  heapStack := h :: !heapStack;
  h

(*
let mkUArrImp a b c d e f =
  heapStack := List.tl (List.tl !heapStack);
  UArr(a,b,c,d,e,f)
*)

let popDHeap () =
  heapStack := List.tl !heapStack

let freshenCell = function
  | HConc(x,s) -> HConc (freshVar x, ty (PEq (theV, wVar x)))
  | HConcObj(x,s,l') -> HConcObj (freshVar x, ty (PEq (theV, wVar x)), l')

let sameHeap () =
  let (hs,cs) = List.hd !heapStack in
  let cs = List.map (fun (l,hc) -> (l, freshenCell hc)) cs in
  (hs, cs)

let sameCell l =
  try freshenCell (List.assoc l (snd (List.hd !heapStack)))
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
%token
  EOF TAG (* TRUE FALSE *) LET REC EQ IN FUN ARROW IF THEN ELSE
  LPAREN RPAREN LBRACE RBRACE LBRACK RBRACK (* ALL *) DOT COMMA
  SEMI DCOLON COLON AS GT (* GTGT *) EXTERN FAIL (* VTRUE VFALSE *) PIPE
  OR IMP IFF NOT AND ITE HAS SEL UPD EQMOD DOM WBOT EMPTY
  TYPE NULL NULLBOX NEW (* LIST *) BANG QMARK
  (* TODO get rid of the sugar tokens *)
  SUGAR_INT SUGAR_BOOL SUGAR_TOP SUGAR_DICT SUGAR_BOT
  SUGAR_INTORBOOL SUGAR_STR SUGAR_INTORSTR SUGAR_STRORBOOL SUGAR_NUM
  SUGAR_EXTEND SUGAR_FLD
  PLUS MINUS MUL DIV LT LE GE (* NE EQEQ AMPAMP PIPEPIPE *) PLUSPLUS
  ASSGN (* LOCALL *) NEWREF REFTYPE (* AT *) MAPSTO SAME HEAP
  FRZN THWD FREEZE THAW REFREEZE
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
%type <Lang.loc * Lang.loc option> jsObjLocs
%type <Lang.frame> jsWhile
%type <Lang.uarr> jsCtor
%type <(Lang.typs * Lang.locs * Lang.heaps) * Lang.loc> jsNew
%type <Lang.loc * Lang.typ> jsArrLit
%type <string> jsFail


%start prog prelude
%start jsTyp jsPolyArgs jsLoc jsObjLocs jsWhile jsFail jsCtor jsNew jsArrLit


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
 | NULL            { Null }
 | UNDEF           { Undef }

value :
 | x=baseval                                   { VBase x }
 | x=VAR                                       { VVar x }
 | EMPTY                                       { VEmpty }
 | LPAREN x=value WITH y=value EQ z=value RPAREN { VExtend(x,y,z) } 
 (* quick hack: using begin/end to avoid conflicts *)
 | BEGIN e=lambda END
     { match Anf.coerce e with (* no grammar for ANF exps, so coerce *)
         | EVal(v) -> v 
         | _ -> printParseErr "coerce lambda"}

exp :
 | exp1                                   { $1 }
 | IF exp THEN exp ELSE exp               { EIf($2,$4,$6) }
 | LET x=varopt EQ e1=exp IN e2=exp       { ELet(x,None,e1,e2) }
 | LET x=varopt a=ann EQ e1=exp IN e2=exp { ELet(x,Some(a),e1,e2) }
 (* | LET REC VAR DCOLON scm EQ exp IN exp  { ParseUtils.mkLetRec $3 $5 $7 $9 } *)
 | EXTERN VAR DCOLON typ exp             { EExtern($2,$4,$5) }
 | HEAP heap exp                         { EHeap($2,$3) }
 | x=LBL LBRACE e=exp RBRACE             { ELabel(x,None,e) }
(*
 | x=LBL DCOLON a=ann LBRACE e=exp RBRACE { ELabel($1,Some($3),$5) }
*)
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
 | NEWREF l=loc e=exp2           { ENewref(l,e) }
 | NEW LPAREN e1=exp COMMA l1=loc COMMA e2=exp COMMA l2=loc RPAREN
     { ENewObj(e1,l1,e2,l2) }
 | FREEZE LPAREN l=loc COMMA e=exp RPAREN    { EFreeze(l,e) }
 | THAW LPAREN l=loc COMMA e=exp RPAREN      { EThaw(l,e) }
 | REFREEZE LPAREN l=loc COMMA e=exp RPAREN  { ERefreeze(l,e) }

exp2 :
 | v=value                                   { EVal v }
 | e=lambda                                  { e }
 | LPAREN exp RPAREN                         { $2 }
 | LPAREN exp COMMA exps RPAREN              { ParseUtils.mkTupleExp ($2::$4) }
 | LPAREN FAIL STR exp RPAREN                { ETcFail($3,$4) }
 | LPAREN e=exp RPAREN AS f=frame            { EAs("source program",e,f) }
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

 (* the productions that result in mkCurriedFuns match sequences of at
    least two variables to avoid conflicting with pat, which can match
    a single variable *)

 | FUN p=pat ARROW LPAREN e=exp RPAREN
     { mkFun ([],[],[]) p e }
 | FUN x=VAR xs=vars ARROW LPAREN e=exp RPAREN
     { mkCurriedFuns ([],[],[]) (x::xs) e }

 | FUN l=poly_formals p=pat ARROW LPAREN e=exp RPAREN
     { mkFun l p e }
 | FUN l=poly_formals x=VAR xs=vars ARROW LPAREN e=exp RPAREN
     { mkCurriedFuns l (x::xs) e }
 

(*
 | FUN LPAREN VAR COLON typ RPAREN
   DIV heap ARROW exp                    { mkEFunImp [] $3 (Some($5,$8)) $10 }
 | FUN LT vars GT LPAREN VAR COLON typ 
   RPAREN DIV heap ARROW exp             { mkEFunImp $3 $6 (Some($8,$11)) $13 }
 | FUN LT vars GT VAR ARROW exp          { mkEFunImp $3 $5 None $7 }
*)


typ :

 (**** raw refinement types *****)

 | LBRACE x=VAR PIPE p=formula RBRACE     { TRefinement(x,p) }
 | LBRACE p=formula RBRACE                { TRefinement("v",p) }

 (***** delayed macros *****)

 | SUGAR_TOP                              { tyAny }
 | SUGAR_BOT                              { tyFls }
 | b=basetag                              { TBaseUnion([b]) }
 | SUGAR_INT                              { TInt }
(*
 | SUGAR_INTORBOOL                        { tyIntOrBool }
 | SUGAR_INTORSTR                         { tyIntOrStr }
*)
 | SUGAR_STRORBOOL                        { tyStrOrBool }

 (* parens to avoid conflicts *)
 | LPAREN t=typ RPAREN BANG               { TNonNull(t) }
 | LPAREN t=typ RPAREN QMARK              { TMaybeNull(t) }

 | u=typ_term                             { tyTypTerm u }
 (* | LPAREN u=typ_term RPAREN               { tyTypTerm u } *)
 (* | LPAREN u=typ_term RPAREN QMARK         { TMaybeNull (tyTypTerm u) } *)

 (* be careful of conflicts *)
 | l=deptuple                             { TTuple(l) }

 | LBRACE b=basetag PIPE p=formula RBRACE             { TBaseRefine("v",b,p) }
 | LBRACE x=VAR COLON b=basetag PIPE p=formula RBRACE { TBaseRefine(x,b,p) }
 | LBRACE SUGAR_INT PIPE p=formula RBRACE
     { TBaseRefine ("v", tagNum, pAnd [integer theV; p]) }

 (***** syntactic macros *****)

 (* TODO might want to add array tuple to abstract syntax *)
 | LT x=array_tuple_typs GT  { let (ts,b) = x in tyArrayTuple tyArrDefault ts b }

 
basetag :
 (* | SUGAR_INT   { tagInt } *)
 | SUGAR_NUM   { tagNum }
 | SUGAR_BOOL  { tagBool }
 | SUGAR_STR   { tagStr }
 | SUGAR_DICT  { tagDict }

deptuple :
(*
 | LPAREN RPAREN (* () *)      { ([], ParseUtils.mkDepTupleTyp []) }
 | LPAREN deptuple_ RPAREN     { let vars = List.map fst $2 in
                                 (vars, ParseUtils.mkDepTupleTyp $2) }
*)
 (* using square brackets so vartyp and deptuple don't conflict in arr_dom *) 
 | LBRACK RBRACK               { [] }
 | LBRACK l=deptuple_ RBRACK   { l }
(*
 | LPAREN RPAREN (* () *)      { [] }
 | LPAREN l=deptuple_ RPAREN   { l }
*)

(*
deptuple_ :
(* | LPAREN RPAREN (* (()) *)                   { [] } *)
 | LPAREN x=VAR COLON t=typ RPAREN                   { [(x,t)] }
 | LPAREN x=VAR COLON t=typ RPAREN MUL dt=deptuple_  { (x,t) :: dt }
*)

deptuple_ :
 | xt=vartyp                    { [xt] }
 | xt=vartyp COMMA l=deptuple_  { xt :: l }

typ_term :
 | TVAR                                  { UVar($1) }
 | NULLBOX                               { UNull }
 | REFTYPE LPAREN l=loc RPAREN           { URef(l) }
 | u=arrow_typ                           { u }
 | ARRTYPE LPAREN t=typ RPAREN           { UArray(t) }


arrow_typ :

 | xt=arrow_dom ARROW t2=typ
     { UArr (ParseUtils.maybeAddHeapPrefixVar
               (([],[],[]),fst xt,snd xt,emp,t2,emp)) }

 | l=poly_formals xt=arrow_dom ARROW t2=typ
     { UArr (ParseUtils.maybeAddHeapPrefixVar
               (l,fst xt,snd xt,emp,t2,emp)) }

 | xt=arrow_dom DIV h1=dheap ARROW t2=typ DIV h2=rheap
     { popDHeap ();
       UArr (ParseUtils.maybeAddHeapPrefixVar
               (([],[],[]),fst xt,snd xt,h1,t2,h2)) }

 | l=poly_formals xt=arrow_dom DIV h1=dheap ARROW t2=typ DIV h2=rheap
     { popDHeap ();
       UArr (ParseUtils.maybeAddHeapPrefixVar
               (l,fst xt,snd xt,h1,t2,h2)) }



(*
 | xt=vartyp ARROW t2=typ   { UArr(([],[],[]),fst(xt),snd(xt),[],t2,[]) }
 | dt=deptuple ARROW t2=typ { printParseErr "a" }
*)

(* TODO 10/26 do parsing for arrows


 | LPAREN VAR COLON typ RPAREN ARROW typ { UArr([],$2,$4,[],$7,[]) }
 | VAR COLON typ ARROW typ               { UArr([],$1,$3,[],$5,[]) }

 (* TODO TODO TODO
 | dt=deptuple ARROW t2=typ
     { let (x,t1,_,t2,_) = ParseUtils.mkDepTupleArrow dt ([],t2,[]) in
       UArr([],x,t1,[],t2,[]) }
 *)



 | LOCALL l=locs DOT x=var COLON t1=typ DIV h1=dheap ARROW t2=typ DIV h2=rheap
 | LOCALL l=locs DOT LPAREN x=var COLON t1=typ RPAREN DIV h1=dheap ARROW
   t2=typ DIV h2=rheap                   { mkUArrImp l x t1 h1 t2 h2 }
 | LPAREN VAR COLON typ RPAREN DIV dheap ARROW typ DIV rheap
                                         { mkUArrImp [] $2 $4 $7 $9 $11 }
 | VAR COLON typ DIV dheap ARROW typ DIV rheap
                                         { mkUArrImp [] $1 $3 $5 $7 $9 }

 (* TODO maybe try having a general production for:
       VAR COLON | LAREN VAR COLON RPAREN | deptuple
 *)

 | LOCALL l=locs DOT dt=deptuple DIV h1=dheap ARROW t2=typ DIV h2=rheap
     { let (x,t1,h1,t2,h2) = ParseUtils.mkDepTupleArrow dt (h1,t2,h2) in
       mkUArrImp l x t1 h1 t2 h2 }

 | dt=deptuple DIV h1=dheap ARROW t2=typ DIV h2=rheap
     { let (x,t1,h1,t2,h2) = ParseUtils.mkDepTupleArrow dt (h1,t2,h2) in
       mkUArrImp [] x t1 h1 t2 h2 }

*)


(*

(* NOTE: the limitations here in the parser need to be taken into account
   when printing arrows (LangUtils.strTT) *)

*)
arrow_dom :
 | LPAREN xt=vartyp RPAREN  { (fst xt, snd xt) }
 | xt=vartyp                { (fst xt, snd xt) }
(* TODO
 | dt=deptuple              { (dummyBinder (), TTuple dt) }
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
 | LPAREN w=walue DCOLON u=typ_term RPAREN      { PUn(HasTyp(w,u)) }
 | LPAREN w=walue DCOLON u=typ_term BANG RPAREN { pIsBang w u }
(*
 | HEAPHAS LPAREN h=heap COMMA l=loc COMMA k=walue RPAREN { PHeapHas(h,l,k) }
*)
 | LPAREN HEAPHAS h=heap l=loc k=walue RPAREN   { PHeapHas(h,l,k) }
 | LPAREN PACKED w=walue RPAREN                 { packed w }
 | LPAREN INTEGER w=walue RPAREN                { integer w }
 (***** logical connectives *****)
 | b=BOOL                                       { if b then PTru else PFls }
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

rheap :
 | LBRACK RBRACK                                 { ([],[]) }
 | LBRACK l2=rheapcells RBRACK                   { ([],l2) }
 | LBRACK l1=tvars RBRACK                        { (l1,[]) }
 | LBRACK l1=tvars PLUSPLUS l2=rheapcells RBRACK { (l1,l2) }
 | h=TVAR                                        { ([h],[]) }
 | SAME                                          { sameHeap () }

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
 | l=loc MAPSTO x=varopt COLON t=typ { (l,HConc(x,t)) }
 | l=loc MAPSTO LPAREN x=varopt COLON t=typ COMMA l2=loc RPAREN
     { (l,HConcObj(x,t,l2)) }
 | l=loc MAPSTO LPAREN x=thawstate COMMA t=typ COMMA l2=loc RPAREN
     { (l,HWeakObj(x,t,l2)) }

rheapcell :
 | heapcell           { $1 }
 | l=loc MAPSTO SAME  { (l, sameCell l) }
 (* TODO add same token sugar back in here *)
 (* TODO add weak obj *)

thawstate :
 | FRZN       { Frzn }
 | THWD l=loc { Thwd(l) }

varopt:
 | x=VAR                { x }
 | UNDERSCORE           { dummyBinder() }
 
vartyp :
 | x=varopt COLON t=typ { (x,t) }
 | LTUP RTUP              { (dummyBinder (), TTuple []) }
 | LTUP dt=deptuple_ RTUP { (dummyBinder (), TTuple dt) }
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
 | t=typ                             { ([t],false) }
 | t=typ COMMA ELLIPSIS              { ([t],true) }
 | t=typ COMMA att=array_tuple_typs  { let (ts,b) = att in (t::ts,b) }

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

jsObjLocs :
 | l=loc EOF                             { (l, None) }
 | l=loc l2=loc EOF                      { (l, Some l2) }
 (* | LPAREN l=loc COMMA l2=loc RPAREN EOF  { (l, Some l2) } *)

jsCtor: NEW u=arrow_typ EOF { match u with
                                | UArr(arr) -> arr
                                | _ -> printParseErr "jsCtor: impossible"  }

jsNew : x=poly_actuals y=loc EOF  { (x,y) }

jsArrLit :
 | l=loc EOF                             { (l, tyArrDefault) }
 | l=loc ARRTYPE LPAREN t=typ RPAREN EOF { (l, t) }
 | ARRTYPE LPAREN t=typ RPAREN EOF       { (LocConst (freshVar "arrLit"), t) }

%%
