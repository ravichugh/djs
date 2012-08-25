
open Lang

module Id = Utils.IdTable


(* let pr = Printf.printf    use Log.log instead! *)
let spr = Printf.sprintf
let fpr = Printf.fprintf

let (|>) f x = x f


(* not storing these in expressions *)
type pos = Lexing.position * Lexing.position
let pos0 = (Lexing.dummy_pos, Lexing.dummy_pos)

let freshVar =
  (* optimistically removing trailing '_' and 6 digits since they are most
       likely inserted by freshVar to begin with.
     TODO a fool-proof way to do this would be to change identifiers to
     pairs of source-level-string-id and internal-integer-id
  *)
  let removeSuffix x =
    let n = String.length x in
    if n <= 7 then x
    else let suf = String.sub x (n-7) 7 in
         let re = Str.regexp "^_[0-9][0-9][0-9][0-9][0-9][0-9]$" in
         if Str.string_match re suf 0
           then String.sub x 0 (n-7)
           else x
  in
  let c = ref 0 in
  fun x ->
    incr c;
    let x = removeSuffix x in
    spr "%s_%06d" x !c

let freshHVar =
  let c = ref 0 in
  fun () ->
    incr c;
    (* TODO spr "H_%06d" !c *)
    "H_"


(***** Map ********************************************************************)

let mapTyp ?fForm:(fForm=(fun x -> x))
           ?fTT:(fTT=(fun x -> x))
           ?fWal:(fWal=(fun x -> x))
           ?fVal:(fVal=(fun x -> x)) 
           ?onlyTopForm:(onlyTopForm=false)
           t =

  let rec fooTyp = function
    | TRefinement(x,p)   -> TRefinement (x, fooForm p)
    | TQuick(x,qt,p)     -> TQuick (x, fooQuickTyp qt, fooForm p)
    | TBaseUnion(l)      -> TBaseUnion l
    | TNonNull(t)        -> TNonNull (fooTyp t)
    | TMaybeNull(t)      -> TMaybeNull (fooTyp t)
    | TExists _          -> failwith "mapTyp TExists"

  and fooQuickTyp = function
    | QBase(bt)   -> QBase bt
    | QRecd(l,b)  -> QRecd (List.map (fun (f,t) -> (f, fooTyp t)) l, b)
    | QTuple(l,b) -> QTuple (List.map (fun (f,t) -> (f, fooTyp t)) l, b)
    | QBoxes(l)   -> if onlyTopForm then QBoxes l else QBoxes (List.map fooTT l)
                        (* NOTE flag to guard recursing into boxes*)

  and fooForm = function
    | PEq(w1,w2)         -> fForm (PEq (fooWal w1, fooWal w2))
    | PApp(s,ws)         -> fForm (PApp (s, List.map fooWal ws))
    | PHasTyp(w,u)       -> let u = if onlyTopForm then u else fooTT u in
                            fForm (PHasTyp (fooWal w, u))
    | PHeapHas(h,l,w)    -> let h = if onlyTopForm then h else fooHeap h in
                            fForm (PHeapHas (h, l, fooWal w))
    | PConn(s,ps)        -> fForm (PConn (s, List.map fooForm ps))
    | PHas(w,ws)         -> fForm (PHas (fooWal w, List.map fooWal ws))
    | PDomEq(w,ws)       -> fForm (PDomEq (fooWal w, List.map fooWal ws))
    | PEqMod(w1,w2,ws)   -> let ws = List.map fooWal ws in
                            fForm (PEqMod (fooWal w1, fooWal w2, ws))
    | PObjHas(ds,k,h,l)  -> let h = if onlyTopForm then h else fooHeap h in
                            let ds = List.map fooWal ds in
                            fForm (PObjHas (ds, fooWal k, h, l))
    | PAll(x,p)          -> fForm (PAll (x, fooForm p))
    (* | PAll _             -> failwith "mapForm: PAll shouldn't appear" *)

  and fooTT = function
    | UVar(x)       -> fTT (UVar x)
    | UNull         -> fTT UNull
    | URef(al)      -> fTT (URef al)
    | UArray(t)     -> fTT (UArray (fooTyp t))
    | UArrow(l,x,t1,h1,t2,h2) ->
        let (t1,h1) = fooTyp t1, fooHeap h1 in
        let (t2,h2) = fooTyp t2, fooHeap h2 in
        fTT (UArrow (l, x, t1, h1, t2, h2))

  and fooWal = function
    | WVal(v)         -> fWal (WVal (fooVal v))
    | WApp(s,ws)      -> fWal (WApp (s, List.map fooWal ws))
    | WBot            -> fWal WBot
    | WHeapSel(h,l,w) -> let h = if onlyTopForm then h else fooHeap h in
                         fWal (WHeapSel (h, l, fooWal w))
    | WObjSel(ds,k,h,l) ->
        let h = if onlyTopForm then h else fooHeap h in
        let ds = List.map fooWal ds in
        fWal (WObjSel (ds, fooWal k, h, l))

  (* TODO if var elim does not end up using this, might get rid of it *)
  and fooVal v = { v with value = match v.value with
    | VExtend(v1,v2,v3) -> fVal (VExtend (fooVal v1, fooVal v2, fooVal v3))
    | v                 -> fVal v
  }

  (* not doing anything with heap vars *)
  and fooHeap (hs,cs) =
    let cs =
      List.map (function
        | (l,HConc(x,s))       -> (l, HConc (x, fooTyp s))
        | (l,HConcObj(x,s,l')) -> (l, HConcObj (x, fooTyp s, l'))
        | (l,HWeakTok(tok))    -> (l, HWeakTok tok)
      ) cs
    in
    (hs, cs)

  in fooTyp t

let mapForm ?fForm:(fForm=(fun x -> x))
            ?fTT:(fTT=(fun x -> x))
            ?fWal:(fWal=(fun x -> x))
            ?fVal:(fVal=(fun x -> x))
            ?onlyTopForm:(onlyTopForm=false)
            f =
  let t = TRefinement ("dummy", f) in
  match mapTyp ~fForm ~fTT ~fWal ~fVal ~onlyTopForm t with
    | TRefinement("dummy",f') -> f'
    | _ -> failwith "mapForm: should never fail"


(***** Fold *******************************************************************)

(* gives the client access to all formulas, walues, and type terms *)

let foldTyp (fForm: 'a -> formula -> 'a)
            (fTT: 'a -> typterm -> 'a)
            (fWal: 'a -> walue -> 'a) (init: 'a) (t: typ) : 'a =

  let rec fooTyp acc = function
    | TRefinement(_,p)   -> fooForm acc p
    | TBaseUnion _       -> acc
    | TNonNull(t)        -> fooTyp acc t
    | TMaybeNull(t)      -> fooTyp acc t
    | TExists _          -> failwith "foldTyp TExists"

  and fooForm acc = function
    | PEq(w1,w2)         -> let acc = List.fold_left fooWal acc [w1;w2] in
                            fForm acc (PEq (w1, w2))
    | PApp(s,ws)         -> let acc = List.fold_left fooWal acc ws in
                            fForm acc (PApp (s, ws))
    | PHasTyp(w,u)       -> let acc = fooWal acc w in
                            let acc = fooTT acc u in
                            fForm acc (PHasTyp (w, u))
    | PHeapHas(h,l,w)    -> let acc = fooHeap acc h in
                            let acc = fooWal acc w in
                            fForm acc (PHeapHas (h, l, w))
    | PConn(s,ps)        -> let acc = List.fold_left fooForm acc ps in
                            fForm acc (PConn (s, ps))
    | PHas(w,ws)         -> let acc = List.fold_left fooWal acc (w::ws) in
                            fForm acc (PHas (w, ws))
    | PDomEq(w,ws)       -> let acc = List.fold_left fooWal acc (w::ws) in
                            fForm acc (PDomEq (w, ws))
    | PEqMod(w1,w2,ws)   -> let acc = List.fold_left fooWal acc (w1::w2::ws) in
                            fForm acc (PEqMod (w1, w2, ws))
    | PObjHas(ds,k,h,l)  -> let acc = List.fold_left fooWal acc (k::ds) in
                            fooHeap acc h
    | PAll _             -> failwith "foldForm: PAll shouldn't appear"

  and fooTT acc = function
    | UVar(x)       -> fTT acc (UVar x)
    | URef(al)      -> fTT acc (URef al)
    | UNull         -> fTT acc UNull
    | UArray(t) ->
        let acc = fooTyp acc t in
        fTT acc (UArray t)
    | UArrow(l,x,t1,h1,t2,h2) ->
        let acc = fooTyp acc t1 in
        let acc = fooHeap acc h1 in
        let acc = fooTyp acc t2 in
        let acc = fooHeap acc h1 in
        fTT acc (UArrow(l,x,t1,h1,t2,h2))

  and fooWal acc = function
    | WVal(v)         -> fWal acc (WVal v)
    | WApp(s,ws)      -> let acc = List.fold_left fooWal acc ws in
                         fWal acc (WApp (s, ws))
    | WHeapSel(h,l,w) -> let acc = fooHeap acc h in
                         let acc = fooWal acc w in
                         fWal acc (WHeapSel (h, l, w))
    | WBot            -> fWal acc WBot
    | WObjSel(ds,k,h,l) -> let acc = List.fold_left fooWal acc (k::ds) in
                           fooHeap acc h

  and fooHeap acc (_,cs) =
    List.fold_left (fun acc -> function
      | (_,HConc(_,s)) | (_,HConcObj(_,s,_)) -> fooTyp acc s
      | (_,HWeakTok(_)) -> acc
    ) acc cs

  in fooTyp init t

let foldForm fForm init t =
  foldTyp fForm (fun acc _ -> acc) (fun acc _ -> acc) init t

let foldTT fTT init t =
  foldTyp (fun acc _ -> acc) fTT (fun acc _ -> acc) init t


(***** Map Exp ****************************************************************)

let mapExp fE e =
  let rec fooExp = function
    | EVal(v) -> fE (EVal (fooVal v))
    | EDict(es) ->
        fE (EDict (List.map (fun (e1,e2) -> (fooExp e1, fooExp e2)) es))
    | EArray(t,es) -> fE (EArray (t, List.map fooExp es))
    | EFun(poly,x,inWorld,e) -> EFun (poly, x, inWorld, fooExp e)
    | EIf(e1,e2,e3) -> fE (EIf (fooExp e1, fooExp e2, fooExp e3))
    | EApp(poly,e1,e2) -> fE (EApp (poly, fooExp e1, fooExp e2))
    | ELet(x,fo,e1,e2) -> fE (ELet (x, fo, fooExp e1, fooExp e2))
    | EExtern(x,t,e) -> fE (EExtern (x, t, fooExp e))
    | ETcFail(s,e) -> fE (ETcFail (s, fooExp e))
    | EAs(s,e,f) -> fE (EAs (s, fooExp e, f))
    | EAsW(s,e,w) -> fE (EAsW (s, fooExp e, w))
    | ENewref(l,e) -> fE (ENewref (l, fooExp e))
    | EDeref(e) -> fE (EDeref (fooExp e))
    | ESetref(e1,e2) -> fE (ESetref (fooExp e1, fooExp e2))
    | EFreeze(l,x,e) -> fE (EFreeze (l, x, fooExp e))
    | EThaw(l,e) -> fE (EThaw (l, fooExp e))
    | EWeak(l,e) -> fE (EWeak (l, fooExp e))
    | ELabel(l,e) -> fE (ELabel (l, fooExp e))
    | EBreak(l,e) -> fE (EBreak (l, fooExp e))
    | EThrow(e) -> fE (EThrow (fooExp e))
    | ETryCatch(e1,x,e2) -> fE (ETryCatch (fooExp e1, x, fooExp e2))
    | ETryFinally(e1,e2) -> fE (ETryFinally (fooExp e1, fooExp e2))
    | ENewObj(e1,l1,e2,l2) -> fE (ENewObj (fooExp e1, l1, fooExp e2, l2))
    | ELoadSrc(s,e) -> fE (ELoadSrc (s, fooExp e))
    | ELoadedSrc(s,e) -> fE (ELoadedSrc (s, fooExp e))
  and fooVal v = { v with value = match v.value with
    | VBase(bv) -> VBase bv
    | VVar(x) -> VVar x
    | VEmpty -> VEmpty
    | VNewObjRef(i) -> VNewObjRef i
    | VExtend(v1,v2,v3) -> VExtend (fooVal v1, fooVal v2, fooVal v3)
    | VArray(t,vs) -> VArray (t, List.map fooVal vs)
    | VTuple(vs) -> VTuple (List.map fooVal vs)
    | VFun(poly,x,inWorld,e) -> VFun (poly, x, inWorld, fooExp e)
  }
  in fooExp e


(***** Fold Exp ***************************************************************)

let foldExp fE fV init e =
  let rec fooExp acc exp = match exp with
    | EVal(v) -> fE (fooVal acc v) exp
    | EDict(es) ->
        let acc = List.fold_left
                    (fun acc (e1,e2) -> fooExp (fooExp acc e1) e2) acc es in
        fE acc exp
    | EArray(t,es) -> fE (List.fold_left fooExp acc es) exp
    | EFun(poly,x,inWorld,e) -> fE (fooExp acc e) exp
    | EIf(e1,e2,e3) -> fE (List.fold_left fooExp acc [e1;e2;e3]) exp
    | EApp(poly,e1,e2) -> fE (List.fold_left fooExp acc [e1;e2]) exp
    | ELet(x,fo,e1,e2) -> fE (List.fold_left fooExp acc [e1;e2]) exp
    | EExtern(x,t,e) -> fE (fooExp acc e) exp
    | ETcFail(s,e) -> fE (fooExp acc e) exp
    | EAs(s,e,f) -> fE (fooExp acc e) exp
    | EAsW(s,e,w) -> fE (fooExp acc e) exp
    | ENewref(l,e) -> fE (fooExp acc e) exp
    | EDeref(e) -> fE (fooExp acc e) exp
    | ESetref(e1,e2) -> fE (List.fold_left fooExp acc [e1;e2]) exp
    | EFreeze(l,x,e) -> fE (fooExp acc e) exp
    | EThaw(l,e) -> fE (fooExp acc e) exp
    | EWeak(l,e) -> fE (fooExp acc e) exp
    | ELabel(l,e) -> fE (fooExp acc e) exp
    | EBreak(l,e) -> fE (fooExp acc e) exp
    | EThrow(e) -> fE (fooExp acc e) exp
    | ETryCatch(e1,x,e2) -> fE (List.fold_left fooExp acc [e1;e2]) exp
    | ETryFinally(e1,e2) -> fE (List.fold_left fooExp acc [e1;e2]) exp
    | ENewObj(e1,l1,e2,l2) -> fE (List.fold_left fooExp acc [e1;e2]) exp
    | ELoadSrc(s,e) -> fE (fooExp acc e) exp
    | ELoadedSrc(s,e) -> fE (fooExp acc e) exp
  and fooVal acc v = match v.value with
    | VBase(bv) -> fV acc v.value
    | VVar(x) -> fV acc v.value
    | VEmpty -> fV acc v.value
    | VNewObjRef(i) -> fV acc v.value
    | VExtend(v1,v2,v3) -> fV (List.fold_left fooVal acc [v1;v2;v3]) v.value
    | VArray(t,vs) -> fV (List.fold_left fooVal acc vs) v.value
    | VTuple(vs) -> fV (List.fold_left fooVal acc vs) v.value
    | VFun(poly,x,inWorld,e) -> fV (fooExp acc e) v.value
  in fooExp init e


(***** Helpers for Abstract Syntax Programming ********************************)

let tag w         = WApp ("tag", [w])
let sel w1 w2     = WApp ("sel", [w1; w2])
let upd w1 w2 w3  = WApp ("upd", [w1; w2; w3])

let has w1 w2     = PHas (w1, [w2])
let eqmod x y zs  = PEqMod (x, y, zs)
let hastyp w ut   = PHasTyp (w, ut)

let plus w1 w2    = WApp ("l_plus", [w1; w2])
let minus w1 w2   = WApp ("l_minus", [w1; w2])

let arrlen x      = WApp ("len", [x])
let packed x      = PApp ("packed", [x])

let lt w1 w2      = PApp ("l_lt", [w1; w2])
let le w1 w2      = PApp ("l_le", [w1; w2])
let gt w1 w2      = PApp ("l_gt", [w1; w2])
let ge w1 w2      = PApp ("l_ge", [w1; w2])

let eq w1 w2      = PEq (w1, w2)

let integer w     = PApp ("integer", [w])

let vBool x       = {pos = pos0; value = VBase (Bool x)}
let vStr x        = {pos = pos0; value = VBase (Str x)}
let vInt x        = {pos = pos0; value = VBase (Int x)}
let vNull         = {pos = pos0; value = VNull}
let vUndef        = {pos = pos0; value = VBase Undef}
let vVar x        = {pos = pos0; value = VVar x}
let vEmpty        = {pos = pos0; value = VEmpty}
let vBase x       = {pos = pos0; value = VBase x}
let vNewObjRef i  = {pos = pos0; value = VNewObjRef i}

let vProj i       = vStr (string_of_int i)

let eStr x        = EVal (vStr x)
let eVar x        = EVal (vVar x)
let wVar x        = WVal (vVar x)
let theV          = wVar "v"

let mkApp f args =
  let rec foo = function
    | []    -> failwith "eApp: no args"
    | x::[] -> EApp (([],[],[]), f, x)
    | x::l  -> EApp (([],[],[]), foo l, x)
  in
  foo (List.rev args)

let wBool x       = WVal (vBool x)
let wStr x        = WVal (vStr x)
let wInt x        = WVal (vInt x)
let wNull         = WVal vNull
let wUndef        = WVal vUndef
let wProj i       = WVal (vProj i)

let pAnd ps       = PConn ("and", ps)
let pOr ps        = PConn ("or", ps)
let pTru          = pAnd []
let pFls          = pOr []
let pImp p q      = PConn ("implies", [p; q])
let pIff p q      = PConn ("iff", [p; q])
let pNot p        = PConn ("not", [p])
let pIte p q r    = pAnd [pImp p q; pImp (pNot p) r]

let conjunctsOf = function PConn("and",l) -> l | p -> [p]
let disjunctsOf = function PConn("or",l)  -> l | p -> [p]

let rec simplify = function
  | PConn("and",[p]) -> p
  | PConn("and",l) ->
      l |> List.map conjunctsOf |> List.concat |> List.map simplify |> pAnd
  | PConn("or",[p]) -> p
  | PConn("or",l) ->
      l |> List.map disjunctsOf |> List.concat |> List.map simplify |> pOr
  | p -> p

let pAnd ps       = simplify (pAnd ps)
let pOr ps        = simplify (pOr ps)

let pFalsy x      = pOr [eq x (wBool false); eq x wNull; eq x wUndef;
                         eq x (wStr ""); eq x (wInt 0)] (* TODO add NaN *)
let pTruthy x     = pNot (pFalsy x)
let pInt          = pAnd [eq (tag theV) (wStr tagNum); integer theV]
let pNum          = PEq (tag theV, wStr tagNum)
let pBool         = PEq (tag theV, wStr tagBool)
let pStr          = PEq (tag theV, wStr tagStr)
let pDict         = PEq (tag theV, wStr tagDict)
let pGuard x b    = PEq (WVal x, WVal (vBool b))
let pIsBang a u   = pAnd [pNot (PEq (a, wNull)); hastyp a u]

let ty p          = TRefinement ("v", p)
let tyAny         = ty pTru (* TTop (* ty PTru *) *)
let tyFls         = ty pFls (* TBot (* ty PFls *) *)
let tyInt         = TQuick ("v", QBase BInt, pTru) 
let tyNum         = TQuick ("v", QBase BNum, pTru) (* ty pNum *)
let tyBool        = TQuick ("v", QBase BBool, pTru) (* ty pBool *)
let tyStr         = TQuick ("v", QBase BStr, pTru) (* ty pStr *)
let tyDict        = TQuick ("v", QRecd ([], false), pTru) (* ty pDict *)
let tyEmpty       = TQuick ("v", QRecd ([], true), eq theV (WVal vEmpty))

let tyNumOrBool   = TBaseUnion [BNum; BBool] (* tagNum; tagBool] *)
let tyStrOrBool   = TBaseUnion [BStr; BBool] (* [tagStr; tagBool] *)
let tyIntOrBool   = TBaseUnion [BInt; BBool] (* ty (pOr [pInt; pBool]) *)
let tyIntOrStr    = TBaseUnion [BInt; BStr] (* ty (pOr [pInt; pStr]) *)

let tyNull        = TQuick ("v", QBoxes [UNull], eq theV wNull)
let tyRef l       = TQuick ("v", QBoxes [URef l], pTru)

let tyTypTerm = function
  | URef(l) -> tyRef l (* so that default for references can be tweaked *)
  | u       -> TQuick ("v", QBoxes [u], pTru)

let tyDepTuple l =
  TQuick ("v", QTuple (List.map (fun (x,t) -> (Some x, t)) l, false), pTru)

let bindersOfDepTuple l =
  List.fold_left (fun acc -> function Some(x) -> x::acc | None -> acc)
    [] (List.map fst l)

(* setting the default for array tuple invariants to be v != undefined,
   not Top, so that packed array accesses can at least prove that the
   value retrieved is not undefined *)
let tyNotUndef = ty (pNot (eq theV (WVal vUndef)))
let tyArrDefault = tyNotUndef

let baseTypToForm = function
  | BNum   -> pNum
  | BInt   -> pInt
  | BStr   -> pStr
  | BBool  -> pBool
  | BUndef -> eq (tag theV) (wStr tagUndef)

(* maybeValOfSingleton used by TcDref3 and Sub to manipulate heap bindings with
   singleton types. can make maybeValOfWal better by "evaluating" record walues
   to values *)

let rec maybeValOfWal = function
  | WVal(v) -> Some v
  | _ -> None

let valToSingleton v = ty (PEq (theV, WVal v))

let maybeValOfSingleton = function
  | TRefinement("v",PEq(WVal({value=VVar"v"}),w)) -> maybeValOfWal w
  | _ -> None

let valOfSingleton t =
  match maybeValOfSingleton t with
    | Some(v) -> v
    | None -> failwith (spr "valOfSingleton: %s" "")


(***** Id Tables **************************************************************)

let oc_boxes = open_out (Settings.out_dir ^ "boxes.txt")

(***** Strings *****)

(*
let isTag s =
  List.exists ((=) s) [tagInt; tagStr; tagBool; tagDict; tagFun]
*)

(*
(* TODO quick, but somewhat dangerous, way to set up tags for JavaScript
   without changing any tags of System D primitives. *)
let switchJsString = function
  | "number"  -> "Int"
  | "boolean" -> "Bool"
  | "string"  -> "Str"
  | "object"  -> "Dict"
  | s         -> s
*)

let idStrings = Id.create ()

let getStringId s = (* assigning ids on demand *)
(*
  let s =
    if !Settings.djsMode
      then switchJsString s
      else s in
*)
  let b = not (Id.mem idStrings s) in
  let i = Id.process idStrings s in
  if b then fpr oc_boxes "\nstring %d\n  \"%s\"\n" i s;
  i

let _ = (* the ids for these strings need to match theory.lisp *)
  assert (1 = getStringId tagDict);
  assert (2 = getStringId tagNum);
  assert (3 = getStringId tagBool);
  assert (4 = getStringId tagStr);
  assert (5 = getStringId tagFun);
  assert (6 = getStringId "TagBot");
  assert (7 = getStringId tagObj);
  assert (8 = getStringId tagUndef);
  assert (9 = getStringId tagRef);
  (* assert (10 = getStringId tagArray); *)
  ()

(***** Boxes *****)

let idTypTerms = Id.create ()
let idHeapTerms = Id.create ()
let idLocTerms = Id.create ()
let idLamTerms = Id.create ()

(* checking by equality if type term already registered *)
let isNewBox x = not (Id.mem idTypTerms x)
let isNewHeapBox x = not (Id.mem idHeapTerms x)
let isNewLocBox x = not (Id.mem idLocTerms x)
let isNewLamBox x = not (Id.mem idLamTerms x)


(***** Skolems for floats *****)

let idSkolems = Id.create ()


(***** Lambdas *****)

(* as long as ANFer prevents lambdas from appearing as arguments to functions
   (and binds them to variables first), then should not have to worry about
   substituting lambdas into types, and so logic should not have to worry
   about reasoning about function values. *)


(***** ... *****)

let newObjId =
  let c = Utils.Counter.create () in
  fun () -> Utils.Counter.next c


(***** Printing to SMT-LIB-2 format and stdout ********************************)

let pretty = ref true

let sugarArrow = ref true (* TODO is this necessary? *)

let rec strPat = function
  | PLeaf(x) -> x
  | PNode(l) -> spr "(%s)" (String.concat "," (List.map strPat l))

let strPato = function
  | Some(p) -> strPat p
  | None    -> "_"

let strLoc = function
  | LocVar(x)   -> x
  | LocConst(x) -> x

let strLocs l = String.concat "," (List.map strLoc l)

let strThawState = function
  | Frzn    -> "frzn"
  | Thwd(l) -> spr "thwd %s" (strLoc l)

let strTag = function
  | "number"  -> "Num"
  | "string"  -> "Str"
  | "boolean" -> "Bool"
  | t         -> t

let strBaseTyp = function
  | BNum   -> "Num"
  | BInt   -> "Int"
  | BStr   -> "Str"
  | BBool  -> "Bool"
  | BUndef -> "Undef"

let strBaseValue v =
  match v, !pretty with
    | Bool(b), true -> spr "%b" b
    | Bool(b), false -> if b then "VTrue" else "VFalse"
    | Undef, _      -> "undefined"
    | Int(i), true  -> spr "%d" i
    | Int(i), false -> spr "(VInt %d)" i
(*
    | Str(s), true  -> spr "\"%s\""
                         (if !Settings.djsMode then switchJsString s else s)
*)
    | Str(s), true  -> spr "\"%s\"" s
    | Str(s), false -> spr "(VStr %d)" (getStringId s)

let rec strVal v = match v.value with
  | VBase(c)    -> strBaseValue c
  | VNull       -> "null"
  | VVar(x)     -> x
  | VEmpty      -> "empty"
  | VNewObjRef(i) -> spr "(VObjRef %d)" i
  | VFun _ as v -> spr "(VFun %d)" (Id.process idLamTerms v)
  | VExtend(v1,v2,v3) ->
      (* spr "(VExtend %s %s %s)" (strVal v1) (strVal v2) (strVal v3) *)
      (* spr "(upd %s %s %s)" (strVal v1) (strVal v2) (strVal v3) *)
      if !pretty then
        spr "(%s with %s = %s)" (strVal v1) (strVal v2) (strVal v3)
      else
        spr "(upd %s %s %s)" (strVal v1) (strVal v2) (strVal v3)
  (* TODO *)
  | VArray(_,vs) ->
      if !pretty then
        spr "<%s> as Arr(_)" (String.concat " " (List.map strVal vs))
      else failwith "strVal VArray"
  | VTuple(vs) ->
      if !pretty then spr "(%s)" (String.concat ", " (List.map strVal vs))
      else (* TODO morally, this should go in embedForm *)
        strVal (Utils.fold_left_i
                  (fun d v i -> wrapVal pos0 (VExtend (d, vProj i, v)))
                  vEmpty vs)

let strFunSym s =
  if !pretty = false then s
  else match s with
    | "l_plus"  -> "+"
    | "l_minus" -> "-"
    | _         -> s

let strPredSym s =
  if !pretty = false then s
  else match s with
    | "l_lt" -> "<"
    | "l_le" -> "<="
    | "l_gt" -> ">"
    | "l_ge" -> ">="
    | _      -> s

let strStrs l = String.concat "," l

let rec strWal = function
  | WVal(v) -> strVal v
  | WApp(s,ws) ->
      spr "(%s %s)" (strFunSym s) (String.concat " " (List.map strWal ws))
  | WBot -> "bot"
  | WHeapSel((h,[]),l,k) ->
      if !pretty then
        spr "(heapsel %s %s %s)" (strHeap (h,[])) (strLoc l) (strWal k)
      else
        let ih = registerHeap (h,[]) in
        let il = registerLoc l in
        spr "(heapsel %d %d %s)" ih il (strWal k)
  | WHeapSel((hs,cs),l,k) ->
      if !pretty then
        spr "(heapsel %s %s %s)" (strHeap (hs,cs)) (strLoc l) (strWal k)
      else
        failwith "strWal HeapSel: constraints not expanded"
  | WObjSel(ds,k,(h,[]),l) ->
      spr "(objsel %s %s %s %s)"
        (strWalList ds) (strWal k) (strHeap (h,[])) (strLoc l)
  | WObjSel(ds,k,h,l) ->
      if !pretty then
        spr "(objsel %s %s %s %s)"
          (strWalList ds) (strWal k) (strHeap h) (strLoc l)
      else
        let _ = pretty := true in
        Log.printTcErr
          ["WObjSel should not have loc constraints:\n";
           spr "WObjSel(%s, %s, %s, %s)" "..."
             (strWal k) (strLoc l) (strHeap h)]

and strWalSet l =
  spr "{%s}" (String.concat "," (List.map strWal l))

and strWalList l =
  spr "[%s]" (String.concat "," (List.map strWal l))

and strTyp = function
  | t when t = tyDict    -> "Dict"
  | t when t = tyNum     -> "Num"
  | t when t = tyInt     -> "Int"
  | t when t = tyBool    -> "Bool"
  | t when t = tyStr     -> "Str"
  | TBaseUnion(l)        -> String.concat "Or" (List.map strBaseTyp l)
  | TRefinement("v",p)   -> spr "{%s}" (strForm p)
  | TRefinement(x,p)     -> spr "{%s|%s}" x (strForm p)
  | TQuick(_,QRecd(l,true),_)  -> strQuickTyp (QRecd (l, true))
  | TQuick(_,QTuple(l,true),_) -> strQuickTyp (QTuple (l, true))
  | TQuick(_,QBoxes([u]),p) when p = pTru -> strTT u
  | TQuick("v",(QBase(_) as qt),p) 
  | TQuick("v",(QRecd(_) as qt),p) 
  | TQuick("v",(QTuple(_) as qt),p) when p = pTru -> strQuickTyp qt
  | TQuick("v",qt,p)     -> spr "{%s|%s}" (strQuickTyp qt) (strForm p)
  | TQuick(x,qt,p)       -> spr "{%s:%s|%s}" x (strQuickTyp qt) (strForm p)
  | TNonNull(t)          -> spr "(%s)!" (strTyp t)
  | TMaybeNull(t)        -> spr "(%s)?" (strTyp t)
  | TExists(x,t,s)       -> spr "exists (%s:%s). %s" x (strTyp t) (strTyp s)

and strQuickTyp = function
  | QBase(bt) -> strBaseTyp bt
  | QBoxes(us) -> strForm (pAnd (List.map (hastyp theV) us))
  | QRecd(l,b) ->
      spr "[%s%s]"
        (String.concat "; "
          (List.map (fun (f,t) -> spr "\"%s\":%s" f (strTyp t)) l))
        (if b then "; exact" else "")
  | QTuple(l,b) ->
      spr "[%s%s]"
        (String.concat ", "
          (List.map (function (Some(x),t) -> spr "%s:%s" x (strTyp t)
          (* TODO remove underscore when parser allows it *)
                            | (None   ,t) -> spr "_:%s" (strTyp t)) l))
          (*                | (None   ,t) -> strTyp t) l)) *)
        (if b then "; exact" else "")

and strTT = function
  | UVar(x) -> x
  | URef(l) -> spr "Ref(%s)" (strLoc l)
  | UArray(t) -> spr "Arr(%s)" (strTyp t)
  | UNull   -> "Null"

  | UArrow(([],[],[]),x,t1,h1,t2,h2) ->
      failwith "strTT: how can arrow have no heap vars?"

(* can't just use this to pretty print arrows without prefix var, since
   would have to check whether the var appears in the types!

  TODO do the pretty printing if h does not appear free in t1 or t2

  (* special case when single heap variable *)
  | UArr((ts,ls,[h]),x,t1,([h1],cs1),t2,([h2],cs2))
    when h = h1 && h = h2 && !sugarArrow ->
      strArrow ((ts,ls,[]),x,t1,([],cs1),t2,([],cs2))
*)

  | UArrow(arr) -> strArrow arr

(*
  | UArr((ts,ls,hs),x,t1,h1,t2,h2) ->
      let s0 =
        if (ts,ls,hs) = ([],[],[]) then ""
        else spr "[%s;%s;%s] " (String.concat "," ts)
                               (String.concat "," ls)
                               (String.concat "," hs)
      in
      let sh1 = if h1 = ([],[]) then "" else spr " / %s" (strHeap h1) in
      let sh2 = if h2 = ([],[]) then "" else spr " / %s" (strHeap h2) in
      spr "%s(%s:%s)%s -> %s%s" s0 x (strTyp t1) sh1 (strTyp t2) sh2
*)

and strArrow (polyArgs,x,t1,e1,t2,e2) =
  let s0 =
    match polyArgs with
      | [],[],[] -> ""
      (* | ts,ls,[] -> spr "[%s;%s] " (strStrs ts) (strStrs ls) *)
      | ts,ls,hs -> spr "[%s;%s;%s] " (strStrs ts) (strStrs ls) (strStrs hs)
  in
  let se1 = if e1 = ([],[]) then "" else spr " / %s" (strHeap e1) in
  let se2 = if e2 = ([],[]) then "" else spr " / %s" (strHeap e2) in
(*
  spr "%s(%s:%s)%s -> %s%s" s0 x (strTyp t1) se1 (strTyp t2) se2
*)
  (* TODO 11/27: optimistically assuming that if t1 is dep tuple, then
     it's binder is trivial. i.e. assuming that the [[ ]] syntax works *)
  let strDom =
    match t1 with
      (* | TTuple _ -> spr "[%s]" (strTyp t1) *)
      | TQuick(_,QTuple(_),_) -> spr "[%s]" (strTyp t1)
      | _        -> spr "(%s:%s)" x (strTyp t1)
  in
  spr "%s%s%s -> %s%s" s0 strDom se1 (strTyp t2) se2
(*
  (* hacking to satisfy parser quirks *)
  match t1 with
    | TTuple _ -> (* TODO remove this special case when deptuples are allowed
                     to appear anywhere by parser *)
        spr "%s%s%s -> %s%s" s0 (strTyp t1) se1 (strTyp t2) se2
    | _ ->
        spr "%s(%s:%s)%s -> %s%s" s0 x (strTyp t1) se1 (strTyp t2) se2
*)

and strForm = function
  | p when p = pTru -> if !pretty then "TRU" else "true"
  | p when p = pFls -> if !pretty then "FLS" else "false"
  | PEq(w1,w2)      -> spr "(= %s %s)" (strWal w1) (strWal w2)
  | PApp(s,ws)      -> spr "(%s %s)" (strPredSym s)
                         (String.concat " " (List.map strWal ws))
  | PConn(s,l)      -> strFormExpanded s l
  | PAll(x,p)       -> spr "(forall ((%s DVal)) %s)" x (strForm p)
  (* TODO make the call to registerBox somewhere more appropriate *)
  | PHasTyp(w,u) ->
      if !pretty
        then spr "(%s :: %s)" (strWal w) (strTT u)
        (*else spr "(= (hastyp %s (Box %d)) true)" (strWal w) (registerBox u)*)
        else spr "(= (hastyp %s %d) true)" (strWal w) (registerBox u)
  | PHeapHas((h,[]),l,k) ->
      if !pretty then
        spr "(heaphas %s %s %s)" (strHeap (h,[])) (strLoc l) (strWal k)
      else
        let ih = registerHeap (h,[]) in
        let il = registerLoc l in
        spr "(heaphas %d %d %s)" ih il (strWal k)
  | PHeapHas(h,l,k) ->
      if !pretty then 
        spr "(heaphas %s %s %s)" (strHeap h) (strLoc l) (strWal k)
      else
        let _ = pretty := true in
        Log.printTcErr
          ["PHeapHas should not have loc constraints:\n";
           spr "HeapHas(%s, %s, %s)" (strHeap h) (strLoc l) (strWal k)]
  (* NOTE: if one of these failwiths triggers, might be because not calling
     a prettyStr* function instead of str* *)
  | PHas(w,ws) ->
      if !pretty
        then spr "(has %s %s)" (strWal w) (strWalSet ws)
        else failwith "strForm: PHas should have been expanded"
        (* else strForm (expandPHas w ws) *)
  | PDomEq(w,ws) ->
      if !pretty
        then spr "(dom %s %s)" (strWal w) (strWalSet ws)
        else failwith "strForm: PDomEq should have been expanded"
        (* else expandPDomEq w ws *)
  | PEqMod(w1,w2,ws) ->
      if !pretty
        then spr "(eqmod %s %s %s)" (strWal w1) (strWal w2) (strWalSet ws)
        else failwith "strForm: PEqMod should have been expanded"
        (* else expandPEqMod w1 w2 ws *)
  | PObjHas(ds,k,h,l) ->
      if !pretty
        then spr "(objhas %s %s %s %s)"
               (strWalList ds) (strWal k) (strHeap h) (strLoc l)
        else failwith "strForm: PObjHas should have been expanded"

(* TODO reorganize options for printing *)
and strFormExpanded conn l =
  if !pretty then
    spr "(%s %s)" conn (String.concat " " (List.map strForm l))
  else begin
  incr depth;
  incr depth;
  let s =
    l |> List.map strForm
      |> List.map (spr "%s%s" (indent()))
      |> String.concat "\n"
      |> spr "(%s\n%s)" conn in
  decr depth;
  decr depth;
  s
  end

(* TODO abstract the register* functions *)

and registerBox ut =
  let newBox = isNewBox ut in
  let i = Id.process idTypTerms ut in
  let b = !pretty in
  pretty := true;
  if newBox then fpr oc_boxes "\nbox %d\n  %s\n" i (strTTFlat ut);
  pretty := b;
  flush oc_boxes;
  i

and registerLoc l =
  let newBox = isNewLocBox l in
  let i = Id.process idLocTerms l in
  let b = !pretty in
  pretty := true;
  if newBox then fpr oc_boxes "\nloc box %d\n  %s\n" i (strLoc l);
  pretty := b;
  flush oc_boxes;
  i

(* TODO really need this for just heap vars *)
and registerHeap h =
  let newBox = isNewHeapBox h in
  let i = Id.process idHeapTerms h in
  let b = !pretty in
  pretty := true;
  if newBox then fpr oc_boxes "\nheap box %d\n  %s\n" i (strHeap h);
  pretty := b;
  flush oc_boxes;
  i

and strTTFlat u = Str.global_replace (Str.regexp "\n") " " (strTT u)

and strHeapCell = function
  | HConc(None,s)         -> spr "%s" (strTyp s)
  | HConc(Some(x),s)      -> spr "%s:%s" x (strTyp s)
  | HConcObj(None,s,l)    -> spr "(%s, %s)" (strTyp s) (strLoc l)
  | HConcObj(Some(x),s,l) -> spr "(%s:%s, %s)" x (strTyp s) (strLoc l)
  | HWeakTok(ts)          -> strThawState ts

and strHeap (hs,cs) =
  let s = 
    String.concat ", " (List.map
      (fun (l,hc) -> spr "%s |-> %s" (strLoc l) (strHeapCell hc)) cs) in
  match hs, cs with
    | [], _ -> spr "[%s]" s
    (* 11/28: extra space to avoid ]] conflict *)
    | _, [] -> spr "[%s ]" (String.concat "," hs)
    | _     -> spr "[%s ++ %s ]" (String.concat "," hs) s

and strWeakLoc (m,t,l) =
  spr "[%s |-> (%s, %s)]" (strLoc m) (strTyp t) (strLoc l)

and strWorld (s,h) =
  spr "%s / %s" (strTyp s) (strHeap h)

let strFrame (l,h,w) =
  spr "[%s] %s -> %s" (String.concat "," l) (strHeap h) (strWorld w)

let strBinding (x,s) = spr "%s:%s" x (strTyp s)

let strHeapEnvCell = function
  | HEConc(v)      -> spr "%s" (strVal v)
  | HEConcObj(v,l) -> spr "(%s, %s)" (strVal v) (strLoc l)
  | HEWeakTok(ts)  -> strThawState ts

let strHeapEnv (hs,cs) =
  let s = 
    String.concat ", " (List.map
      (fun (l,hc) -> spr "%s |-> %s" (strLoc l) (strHeapEnvCell hc)) cs) in
  match hs, cs with
    | [], _ -> spr "[%s]" s
    (* 11/28: extra space to avoid ]] conflict *)
    | _, [] -> spr "[%s ]" (String.concat "," hs)
    | _     -> spr "[%s ++ %s ]" (String.concat "," hs) s

let formToSMT p =
  pretty := false; let s = strForm p in pretty := true; s

let _ = (* the ids for these boxes need to match theory.lisp *)
  assert (1 = registerBox UNull);
  ()


(***** Free variable computation **********************************************)

module VVars = Set.Make (struct type t = vvar let compare = compare end)
module TVars = Set.Make (struct type t = tvar let compare = compare end)
module LVars = Set.Make (struct type t = lvar let compare = compare end)
module HVars = Set.Make (struct type t = hvar let compare = compare end)

module Quad = struct
  type t = VVars.t * TVars.t * LVars.t * HVars.t

  let empty = (VVars.empty, TVars.empty, LVars.empty, HVars.empty)

  let combine (v1,t1,l1,h1) (v2,t2,l2,h2) =
    (VVars.union v1 v2, TVars.union t1 t2, LVars.union l1 l2, HVars.union h1 h2)

  let combineList l = List.fold_left combine empty l

  let memV v (vs,_,_,_) = VVars.mem v vs
  let memT t (_,ts,_,_) = TVars.mem t ts
  let memL l (_,_,ls,_) = LVars.mem l ls
  let memH h (_,_,_,hs) = HVars.mem h hs

  let addV v (vs,ts,ls,hs) = (VVars.add v vs, ts, ls, hs)
  let addT t (vs,ts,ls,hs) = (vs, TVars.add t ts, ls, hs)
  let addL l (vs,ts,ls,hs) = (vs, ts, LVars.add l ls, hs)
  let addH h (vs,ts,ls,hs) = (vs, ts, ls, HVars.add h hs)

  let addVs xs quad = List.fold_left (fun acc x -> addV x acc) quad xs
end

let depTupleBinders t =
  let rec foo acc = function
(*
    | TTuple(l) -> 
        let (xs,ts) = List.split l in
        let acc = List.fold_left (fun acc x -> x::acc) acc xs in
        List.fold_left foo acc ts
*)
    | TQuick(_,QTuple(l,_),_) -> bindersOfDepTuple l
    | TNonNull(t) | TMaybeNull(t) -> foo acc t
    | _ -> acc
  in foo [] t

let heapBinders (_,cs) =
  List.fold_left
    (fun acc (l,hc) ->
       match hc with HWeakTok _ -> acc
                   | HConc(None,_) | HConcObj(None,_,_) -> acc
                   | HConc(Some(x),_) | HConcObj(Some(x),_,_) -> x::acc)
    [] cs

(* all the freeVarsX functions are of the form env:Quad.t -> x:X -> Quad.t *)

let rec freeVarsVal env v = match v.value with
  | VBase _ -> Quad.empty
  | VVar(x) -> if Quad.memV x env then Quad.empty else Quad.addV x Quad.empty
  | VEmpty  -> Quad.empty
  | VNewObjRef _ -> Quad.empty
  | VExtend(v1,v2,v3) ->
      Quad.combineList (List.map (freeVarsVal env) [v1;v2;v3])
  | VArray(_,vs) | VTuple(vs) ->
      Quad.combineList (List.map (freeVarsVal env) vs)
  | VFun _ -> Quad.empty
      (* TODO might want to recurse into lambdas if they can appear in
         formulas... *)

let rec freeVarsWal env = function
  | WVal(v)    -> freeVarsVal env v
  | WApp(s,ws) -> Quad.combineList (List.map (freeVarsWal env) ws)
  | WBot       -> Quad.empty
  | WHeapSel(h,l,k) ->
      Quad.combineList [freeVarsHeap env h; freeVarsLoc env l; freeVarsWal env k]
  | WObjSel(ds,k,h,l) ->
      Quad.combineList
        [Quad.combineList (List.map (freeVarsWal env) (k::ds));
         freeVarsHeap env h; freeVarsLoc env l]

and (* let rec *) freeVarsTyp env = function
  | TRefinement(x,p) -> freeVarsForm (Quad.addV x env) p
  | TBaseUnion _     -> Quad.empty
  | TQuick(x,qt,p)   -> let v1 = freeVarsForm env p in
                        let v2 = freeVarsQuickTyp env qt in
                        Quad.combineList [v1;v2]
  | TNonNull(t)      -> freeVarsTyp env t
  | TMaybeNull(t)    -> freeVarsTyp env t
  | TExists _        -> failwith "freeVars TExists"

and freeVarsQuickTyp env = function
  | QBase _    -> Quad.empty
  | QBoxes(us) -> Quad.combineList (List.map (freeVarsTT env) us)
  | QRecd(l,_) -> Quad.combineList (List.map (freeVarsTyp env) (List.map snd l))
  | QTuple(l,_) ->
      let binders = bindersOfDepTuple l in
      let env = List.fold_left (fun acc x -> Quad.addV x acc) env binders in
      Quad.combineList (List.map (freeVarsTyp env) (List.map snd l))

and freeVarsForm env = function
  | PEq(w1,w2)       -> Quad.combine (freeVarsWal env w1) (freeVarsWal env w2)
  | PApp(_,ws)       -> Quad.combineList (List.map (freeVarsWal env) ws)
  | PHasTyp(w,u)     -> Quad.combine (freeVarsWal env w) (freeVarsTT env u)
  | PConn(_,ps)      -> Quad.combineList (List.map (freeVarsForm env) ps)
  | PHas(w,ws)       -> Quad.combineList (List.map (freeVarsWal env) (w::ws))
  | PDomEq(w,ws)     -> Quad.combineList (List.map (freeVarsWal env) (w::ws))
  | PEqMod(x,y,z)    -> Quad.combineList (List.map (freeVarsWal env) (x::y::z))
  | PHeapHas(h,l,k)  ->
      Quad.combineList
        [freeVarsHeap env h; freeVarsLoc env l; freeVarsWal env k]
  | PObjHas(ds,k,h,l) ->
      Quad.combineList
        (freeVarsHeap env h :: (List.map (freeVarsWal env) (k::ds)))
  | PAll _           -> failwith "freeVarsForm: PAll shouldn't appear"

and freeVarsTT env = function
  | UNull   -> Quad.empty
  | UVar(x) -> if Quad.memT x env then Quad.empty else Quad.addT x Quad.empty
  | URef(l) -> freeVarsLoc env l
  | UArray(t) -> freeVarsTyp env t
  | UArrow((ts,ls,hs),x,t1,h1,t2,h2) ->
      let env = List.fold_left (fun env t -> Quad.addT t env) env ts in
      let env = List.fold_left (fun env l -> Quad.addL l env) env ls in
      let env = List.fold_left (fun env h -> Quad.addH h env) env hs in
(*
      let env' = List.fold_left (fun env x -> Quad.addV x env) env (x::xs) in
      Quad.combine (freeVarsWorld env (t1,h1)) (freeVarsWorld env' (t2,h2))
*)
      (* 3/30: added depTupleBinders *)
      let env1 = Quad.addVs (x :: depTupleBinders t1) env in
      let env2 = Quad.addVs (heapBinders h1) env1 in
      Quad.combineList
        [freeVarsTyp env t1; freeVarsHeap env1 h1; freeVarsWorld env2 (t2,h2)]

and freeVarsHeap env (hs,cs) =
  let free =
    List.fold_left
    (fun acc h -> if Quad.memH h env then acc else Quad.addH h acc)
    Quad.empty hs in
  let xs = heapBinders (hs,cs) in
  let env = List.fold_left (fun env x -> Quad.addV x env) env xs in
  List.fold_left (fun acc -> function
    | (l,HConc(_,t))
    | (l,HConcObj(_,t,_)) ->
         Quad.combineList [freeVarsLoc env l; freeVarsTyp env t; acc]
    | (l,HWeakTok(_)) ->
         freeVarsLoc env l
  ) free cs

and freeVarsWorld env (t,h) =
  let xs = heapBinders h in
  let env' = List.fold_left (fun env x -> Quad.addV x env) env xs in
  Quad.combine (freeVarsHeap env h) (freeVarsTyp env' t)

and freeVarsLoc env = function
  | LocVar(x)  -> if Quad.memL x env then Quad.empty else Quad.addL x Quad.empty
  | LocConst _ -> Quad.empty


(***** Type substitution ******************************************************)

type vsubst = (vvar * walue) list
type tsubst = (tvar * typ) list
type lsubst = (hvar * loc) list
type hsubst = (hvar * heap) list

module MasterSubst = struct

  type t = vsubst * tsubst * lsubst * hsubst

  let myFilter l sub = List.filter (fun (x,_) -> not (List.mem x l)) sub

  let removeVVars l (vsub,tsub,lsub,hsub) = (myFilter l vsub, tsub, lsub, hsub)
  let removeTVars l (vsub,tsub,lsub,hsub) = (vsub, myFilter l tsub, lsub, hsub)
  let removeLVars l (vsub,tsub,lsub,hsub) = (vsub, tsub, myFilter l lsub, hsub)
  let removeHVars l (vsub,tsub,lsub,hsub) = (vsub, tsub, lsub, myFilter l hsub)

  let extendVSubst l (vsub,tsub,lsub,hsub) =
    (vsub @ l, tsub, lsub, hsub) (* not checking for duplicates *)

  let freeVars (vsub,tsub,lsub,hsub) =
    Quad.combineList (List.concat
      [List.map (freeVarsWal Quad.empty) (List.map snd vsub);
       List.map (freeVarsTyp Quad.empty) (List.map snd tsub);
       List.map (freeVarsLoc Quad.empty) (List.map snd lsub);
       List.map (freeVarsHeap Quad.empty) (List.map snd hsub)])

  let print (vsub,tsub,lsub,hsub) =
    Log.log0 "vsub\n";
    List.iter (fun (x,w) -> Log.log2 "  %s |-> %s\n" x (strWal w)) vsub;
    Log.log0 "tsub\n";
    List.iter (fun (x,t) -> Log.log2 "  %s |-> %s\n" x (strTyp t)) tsub;
    Log.log0 "lsub\n";
    List.iter (fun (x,l) -> Log.log2 "  %s |-> %s\n" x (strLoc l)) lsub;
    Log.log0 "hsub\n";
    List.iter (fun (x,h) -> Log.log2 "  %s |-> %s\n" x (strHeap h)) hsub;
    ()

end

type subst = MasterSubst.t

(* checks whether any of the binders are referred to within the tuple *)
let isDepTuple l =
  let env = Quad.empty in (* since looking for all variable occurrences *)
  let varsMentioned =
    Quad.combineList (List.map (freeVarsTyp env) (List.map snd l)) in
  List.exists (fun x -> Quad.memV x varsMentioned) (bindersOfDepTuple l)


(******
   the substX routines do all four kinds of substitution

     1. value var   -[w/x]
     2. type var    Inst(-,A,T)
     3. loc var     -[l/L]
     4. heap var    -[E/H]

   with capture-avoidance for the two kinds of binding forms

     1. types       {x|p} (and sugar forms {x:B|p} and (x:T,y:S))
     2. arrows      [A_i;L_i;H_i] x:T1/E1 -> T2/E2
*)

let rec substWal (subst:subst) = function
  | WVal(v) -> begin match v.value with
      | VVar(x) -> (* value variable substitution *)
          let (sub,_,_,_) = subst in
          if List.mem_assoc x sub then List.assoc x sub else WVal v
      | VBase _       -> WVal v
      | VEmpty        -> WVal v
      | VNull         -> WVal v
      | VNewObjRef _  -> WVal v
      | VArray _      -> WVal v (* TODO *)
      | VTuple _      -> WVal v (* TODO *)
      | VExtend _     -> WVal v (* TODO *)
      | VFun _        -> WVal v (* lambdas shouldn't appear in formulas *)
    end
  | WBot -> WBot
  | WApp(s,ws) -> WApp (s, List.map (substWal subst) ws)
  | WHeapSel(h,l,w) ->
      WHeapSel (substHeap subst h, substLoc subst l, substWal subst w)
  | WObjSel(ds,k,h,l) ->
      WObjSel (List.map (substWal subst) ds, substWal subst k,
               substHeap subst h, substLoc subst l)

and substForm subst = function
  | PEq(w1,w2)  -> PEq (substWal subst w1, substWal subst w2)
  | PApp(s,ws)  -> PApp (s, List.map (substWal subst) ws)
  | PConn(s,ps) -> PConn (s, List.map (substForm subst) ps)
  | PHasTyp(w,UVar(x)) -> (* type variable instantiation *)
      let w = substWal subst w in
      let (_,sub,_,_) = subst in
      if List.mem_assoc x sub then applyTyp (List.assoc x sub) w
      else PHasTyp (w, UVar x)
  | PHasTyp(w,u) ->
      PHasTyp (substWal subst w, substTT subst u)
  | PHeapHas(h,l,w) ->
      PHeapHas (substHeap subst h, substLoc subst l, substWal subst w)
  | PHas(w,ws) ->
      PHas (substWal subst w, List.map (substWal subst) ws)
  | PDomEq(w,ws) ->
      PDomEq (substWal subst w, List.map (substWal subst) ws)
  | PEqMod(x,y,z) ->
      PEqMod (substWal subst x, substWal subst y, List.map (substWal subst) z)
  | PObjHas(ds,k,h,l) ->
      PObjHas (List.map (substWal subst) ds, substWal subst k,
               substHeap subst h, substLoc subst l)
  | PAll _ -> failwith "substForm: PAll shouldn't appear"

and substTyp (subst:subst) = function
  | TBaseUnion(l)   -> TBaseUnion l
  | TNonNull(t)     -> TNonNull (substTyp subst t)
  | TMaybeNull(t)   -> TMaybeNull (substTyp subst t)
  (* TODO assuming that only one v::A predicate *)
  | TQuick(y,QBoxes([UVar(x)]),p) when p = pTru -> (* type variable inst *)
      let (_,sub,_,_) = subst in
      if List.mem_assoc x sub then List.assoc x sub
      else TQuick (y, QBoxes [UVar x], pTru)
  (* binding forms *)
  | TRefinement(x,p) ->
      let subst = MasterSubst.removeVVars [x] subst in
      let (x,p) = freshenRawTyp (MasterSubst.freeVars subst) x p in
      TRefinement (x, substForm subst p)
  | TQuick(x,qt,p) ->
      let subst = MasterSubst.removeVVars [x] subst in
      let (x,p) = freshenRawTyp (MasterSubst.freeVars subst) x p in
      TQuick (x, substQuickTyp subst qt, substForm subst p)
(*
  | TTuple(l) ->
      let subst = MasterSubst.removeVVars (List.map fst l) subst in
      let l = freshenDepTuple (MasterSubst.freeVars subst) l in
      TTuple (List.map (fun (x,t) -> (x, substTyp subst t)) l)
*)
  | TExists(x,t1,t2) ->
      let (l,_,_,_) = subst in
      if List.mem_assoc x l then failwith "subst TExists" (* TODO 8/20 *)
      else TExists (x, substTyp subst t1, substTyp subst t2)

and substQuickTyp subst = function
  | QBase(bt)  -> QBase bt
  | QBoxes(l)  -> QBoxes (List.map (substTT subst) l)
  | QRecd(l,b) -> QRecd (List.map (fun (f,t) -> (f, substTyp subst t)) l, b)
  | QTuple(l,b) ->
      let binders = bindersOfDepTuple l in
      let subst = MasterSubst.removeVVars binders subst in
      let l = freshenDepTuple (MasterSubst.freeVars subst) l in
      QTuple (List.map (fun (xo,t) -> (xo, substTyp subst t)) l, b)

and substTT subst = function
  | UNull   -> UNull
  | UVar(x) -> UVar x (* note: type instantiation happens at w::A, not here *)
  | URef(l) -> URef (substLoc subst l)
  | UArray(t) -> UArray (substTyp subst t)
  (* binding form *)
  | UArrow((ts,ls,hs),x,t1,h1,t2,h2) ->
      let xs = heapBinders h1 in
      let xs = depTupleBinders t1 @ xs in (* 3/30: added depTupleBinders *)
      let subst =
        subst |> MasterSubst.removeVVars (x::xs)
              |> MasterSubst.removeTVars ts
              |> MasterSubst.removeLVars ls
              |> MasterSubst.removeHVars hs in
      let (substHeapBinders,h1) = freshenHeap (MasterSubst.freeVars subst) h1 in
      let (x',t1)  = freshenDomain (MasterSubst.freeVars subst) x t1 in
      let subst = (* need these because x and xs may appear free in t2/h2 *)
        MasterSubst.extendVSubst ((x, wVar x')::substHeapBinders) subst in
      let t1 = substTyp subst t1 in
      let t2 = substTyp subst t2 in
      let h1 = substHeap subst h1 in
      let h2 = substHeap subst h2 in
      UArrow ((ts,ls,hs), x', t1, h1, t2, h2)

and substHeap subst (hs,cs) =
  let (hs,cs) =
    let (_,_,_,sub) = subst in
    List.fold_left (fun (acc1,acc2) h ->
      if List.mem_assoc h sub then
        let (hActual,cActual) = List.assoc h sub in
        (acc1 @ hActual, acc2 @ cActual)
      else
        (acc1 @ [h], acc2)
    ) ([],cs) hs
    in
  (* at this point, hs are the variables not substituted away and
     cs is the original constraints plus new constraints from actuals *)
  let cs =
    (* binders should've already been refreshed by arrow case to avoid capture *)
    List.map (function
      | (l,HConc(xo,s)) ->
          let subst =
            match xo with
              | None -> subst
              | Some(x) -> MasterSubst.removeVVars [x] subst in
          (substLoc subst l, HConc (xo, substTyp subst s))
      | (l,HConcObj(xo,s,l')) ->
          let subst =
            match xo with
              | None -> subst
              | Some(x) -> MasterSubst.removeVVars [x] subst in
          (substLoc subst l,
           HConcObj (xo, substTyp subst s, substLoc subst l'))
      | (l,HWeakTok(Frzn)) ->
          (substLoc subst l, HWeakTok Frzn)
      | (l,HWeakTok(Thwd(l'))) ->
          (substLoc subst l, HWeakTok (Thwd (substLoc subst l')))
    ) cs
  in
  (hs, cs)

and substLoc subst = function
  | LocConst(x) -> LocConst x
  | LocVar(x) -> (* location variable substitution *)
      let (_,_,sub,_) = subst in
      if List.mem_assoc x sub then List.assoc x sub else LocVar x

(* [[T]](w) *)
and applyTyp t w =
  match t with
    | TNonNull(t)      -> pAnd [applyTyp t w; pNot (PEq (w, wNull))]
    | TMaybeNull(t)    -> pOr [applyTyp t w; PEq (w, wNull)]
    | TBaseUnion(l)    -> pOr (List.map baseTypToForm l)
    | TRefinement(y,f) -> substForm ([(y,w)],[],[],[]) f
    | TQuick(y,qt,f)   -> let f0 = applyQuickTyp (wVar y) qt in
                          substForm ([(y,w)],[],[],[]) (pAnd [f;f0])
    | TExists(x,t,s)   -> failwith (spr "applyTyp TExists\n%s :: %s\n%s\n%s"
                            x (strTyp t) (strTyp s) (strWal w))
(*
    | TTuple(l) ->
        let (vars,typs) = List.split l in
        let subst = Utils.map_i (fun x i -> (x, sel w (wProj i))) vars in
        let subst = (subst,[],[],[]) in
        let has =
          PHas (w, List.map wProj (Utils.list0N (pred (List.length l)))) in
        let sels =
          Utils.map_i
            (fun t i -> applyTyp (substTyp subst t) (sel w (wProj i)))
            typs
        in
        pAnd (PEq (tag w, wStr "Dict") :: has :: sels)
*)

and applyQuickTyp w = function
  | QBase(bt) -> baseTypToForm bt
  | QBoxes(us) -> pAnd (List.map (hastyp w) us)
  | QRecd(l,exactDom) ->
      let ps = List.map (fun (f,t) -> applyTyp t (sel w (wStr f))) l in
      let keys = List.map wStr (List.map fst l) in
      let dom = if exactDom then PDomEq (w, keys) else PHas (w, keys) in
      pAnd (dom::ps)
  | QTuple(l,exactDom) ->
      let subst =
        Utils.fold_left_i (fun acc (xo,_) i ->
          match xo with
            | None    -> acc
            | Some(x) -> (x, sel w (wProj i)) :: acc) [] l in
      let subst = (subst,[],[],[]) in
      let ps =
        Utils.map_i (fun (_,t) i -> 
          substForm subst (applyTyp t (sel w (wProj i)))) l in
      let keys = Utils.map_i (fun _ i -> wProj i) l in
      let dom = if exactDom then PDomEq (w, keys) else PHas (w, keys) in
      pAnd (dom::ps)


(***** the helpers that rename binders to avoid capture *****)

and freshenRawTyp free x p =
  if Quad.memV x free then
    let x' = freshVar x in
    let p' = substForm ([(x, wVar x')],[],[],[]) p in
    (x', p')
  else
    (x, p)

(*
and freshenDepTuple free l =
  let binderSubst =
    List.fold_left
      (fun acc x -> if Quad.memV x free then (x, freshVar x)::acc else acc)
      [] (List.map fst l) in
  let subst = (List.map (fun (x,x') -> (x, wVar x')) binderSubst, [], [], []) in
  List.map (fun (x,t) ->
    let t = substTyp subst t in
    if List.mem_assoc x binderSubst
    then (List.assoc x binderSubst, t)
    else (x, t)
  ) l
*)

and freshenDepTuple free l =
  let binderSubst =
    List.fold_left
      (fun acc -> function
         | Some(x) -> if Quad.memV x free then (x, freshVar x) :: acc else acc
         | None    -> acc
      ) [] (List.map fst l) in
  let subst = (List.map (fun (x,x') -> (x, wVar x')) binderSubst, [], [], []) in
  List.map (fun (xo,t) ->
    let t = substTyp subst t in
    match xo with
      | None    -> (None, t)
      | Some(x) -> if List.mem_assoc x binderSubst
                   then (Some (List.assoc x binderSubst), t)
                   else (Some x, t)) l

and freshenHeap free (hs,cs) =
  let binderSubst =
    List.fold_left (fun acc -> function
      | (_,HConc(None,_)) -> failwith "freshenHeap 1"
      | (_,HConcObj(None,_,_)) -> failwith "freshenHeap 2"
      | (_,HConc(Some(x),_))
      | (_,HConcObj(Some(x),_,_)) ->
          if Quad.memV x free then (x, freshVar x)::acc else acc
      | (_,HWeakTok _) ->
          acc
    ) [] cs
  in
  let binderSubstW = List.map (fun (x,x') -> (x, wVar x')) binderSubst in
  let subst = (binderSubstW,[],[],[]) in
  let cs =
    List.map (function
      | (_,HConc(None,_)) -> failwith "freshenHeap 3"
      | (_,HConcObj(None,_,_)) -> failwith "freshenHeap 4"
      | (l,HConc(Some(x),s)) ->
          let x =
            if List.mem_assoc x binderSubst
            then List.assoc x binderSubst
            else x in
          (l, HConc (Some x, substTyp subst s))
      | (l,HConcObj(Some(x),s,l')) ->
          let x =
            if List.mem_assoc x binderSubst
            then List.assoc x binderSubst
            else x in
          (l, HConcObj (Some x, substTyp subst s, l'))
      | (l,HWeakTok(tok)) ->
          (l, HWeakTok tok)
    ) cs
  in
  (binderSubstW, (hs, cs))

and freshenDomain free x t =
  match freshenDepTuple free [(Some(x),t)] with
    | [(Some(x'),t')] -> (x', t')
    | _               -> failwith "freshenDomain: impossible"

let substTyp subst t =
  BNstats.time "substTyp" (substTyp subst) t


(***** Expression Substitution ************************************************)

(* needed only by the parser, when desugaring letrecs *)

let substVarInExp z x e =
  if x = z then e
  else failwith "substVarInExp: letrec using a freshvar for mono def?"


(***** Expanding pre-formulas *************************************************)

let oc_unroll = open_out (Settings.out_dir ^ "unroll.txt")

let printUnroll cap p q =
  fpr oc_unroll "%s\n%s %s\n\n%s\n\n" (String.make 80 '-') cap
    (strForm p) (strForm q)

let printUnrollWal cap w1 w2 =
  fpr oc_unroll "%s\n%s %s\n\n%s\n\n" (String.make 80 '-') cap
    (strWal w1) (strWal w2)

let sHole i = spr "__hole__%d" i
let wHole i = wVar (sHole i)

(***** expand PHeapHas *****)

let rec expandHH (hs,cs) l k =
  let p =
    if not (List.mem_assoc l cs) then PHeapHas ((hs,[]), l, k)
    else begin
      match List.assoc l cs with
        | HConcObj(None,_,l') -> failwith "expandHH None"
        | HConcObj(Some(d),_,l') -> 
            if l' = lRoot then
              has (wVar d) k
            else
              pOr [has (wVar d) k; expandHH (hs,cs) l' k]
        | _ -> failwith (spr "expandHH: %s" (strLoc l))
    end
  in
  printUnroll "expand" (PHeapHas((hs,cs),l,k)) p;
  p

(***** expand PObjHas *****)

let expandOH ds k (hs,cs) l =
  let rec foo ds l =
    if not (List.mem_assoc l cs) then PObjHas (ds, k, (hs,[]), l)
    else begin
      match List.assoc l cs with
        | HConcObj(None,t,l') -> foo (ds @ [WVal (valOfSingleton t)]) l'
        | HConcObj(Some(d),_,l') -> foo (ds @ [wVar d]) l'
        | _ -> failwith "expandOH: not conc constraint"
    end
  in
  let p = foo ds l in
  printUnroll "expand" (PObjHas(ds,k,(hs,cs),l)) p;
  p

(***** expand WHeapSel *****)

(* trick to expand HeapSel in place, without computing formula contexts
   and applying them: convert to an ObjSel macro! *)
let expandHS (hs,cs) l k =
  let rec foo ds l =
    if not (List.mem_assoc l cs) then WObjSel (ds, k, (hs,[]), l)
    else begin
      match List.assoc l cs with
        | HConcObj(None,_,l') -> failwith "expandHS None"
        | HConcObj(Some(d),_,l') -> foo (ds @ [wVar d]) l'
        | _ -> failwith "expandHS: not conc constraint"
    end
  in
  let w = foo [] l in
  printUnrollWal "expand" (WHeapSel((hs,cs),l,k)) w;
  w

(***** expand WObjSel *****)

let expandOS ds k (hs,cs) l =
  let rec foo ds l =
    if not (List.mem_assoc l cs) then WObjSel (ds, k, (hs,[]), l)
    else begin
      match List.assoc l cs with
        | HConcObj(None,t,l') -> foo (ds @ [WVal (valOfSingleton t)]) l'
        | HConcObj(Some(d),_,l') -> foo (ds @ [wVar d]) l'
        | _ -> failwith "expandOS: not conc constraint"
    end
  in
  let w = foo ds l in
  printUnrollWal "expand" (WObjSel(ds,k,(hs,cs),l)) w;
  w

(***** *****)

let expandPredSymbols = function
  | PHeapHas(e,l,k)   -> expandHH e l k
  | PObjHas(ds,k,e,l) -> expandOH ds k e l
  | p                 -> p

let expandFunSymbols = function
  | WHeapSel(e,l,k)   -> expandHS e l k
  | WObjSel(ds,k,e,l) -> expandOS ds k e l
  | w                 -> w

(* TODO don't want to recurse inside type terms *)
let expandPreTyp t =
  t |> mapTyp ~fForm:expandPredSymbols
    |> mapTyp ~fWal:expandFunSymbols

(*

(* not using mapForm, since want to recurse inside only formulas *)
let rec expandPreForm p =
  match p with
    | PEq _ | PApp _ | PTru | PFls | PUn _
    | PHas _ | PDomEq _ | PEqMod _  -> p
    | PConn(f,ps)       -> PConn (f, List.map expandPreForm ps)
    | PHeapHas(e,l,k)   -> unfoldHH e l k
    | PObjHas(ds,k,e,l) -> unfoldOH ds k e l

let rec expandPreTyp t =
  match t with
    | TTop | TBot | TBaseUnion _ | THasTyp _ -> t
    | TRefinement(x,p) -> TRefinement (x, expandPreForm p)
    | TBaseRefine(x,t,p) -> TBaseRefine (x, t, expandPreForm p)
    | TTuple(l) -> TTuple (List.map (fun (x,t) -> (x, expandPreTyp t)) l)
    | TNonNull(t) -> TNonNull (expandPreTyp t)
    | TMaybeNull(t) -> TMaybeNull (expandPreTyp t)
    | TExists(x,t,s) -> TExists (x, expandPreTyp t, expandPreTyp s)
*)

let expandPreHeap (hs,cs) =
  let cs =
    List.map (fun (l,hc) -> match hc with
      | HConc(x,s)       -> (l, HConc (x, expandPreTyp s))
      | HConcObj(x,s,l') -> (l, HConcObj (x, expandPreTyp s, l'))
      | HWeakTok(tok)    -> (l, HWeakTok tok)
    ) cs
  in
  (hs, cs)


(***** Embedding formulas *****************************************************)

(***** embed PHas *****)

let hasFld d f = pNot (PEq (sel d f, WBot))

let embedHas d = function
  | [k] -> hasFld d k
  | ks  -> pAnd (List.map (hasFld d) ks)

(***** embed PDomEq *****)

let embedDomEq d ks =
  let k' = "_otherKey" in
  pAnd [embedHas d ks;
        PAll (k', pImp (pAnd (List.map (fun k -> pNot (PEq (wVar k', k))) ks))
                       (PEq (sel d (wVar k'), WBot)))]

(***** embed PEqMod *****)

let embedEqMod d1 d2 ks =
  let k' = "_otherKey" in
  pAnd [PEq (tag d1, wStr tagDict);
        PAll (k', pImp (pAnd (List.map (fun k -> pNot (PEq (wVar k', k))) ks))
                       (PEq (sel d1 (wVar k'), sel d2 (wVar k'))))]

(***** embed PObjHas *****)

let rec embedObjHas ds k (hs,cs) l =
  if cs <> [] then
    kill (spr "embedObjHas: constraints should've been expanded:\n\n%s"
      (strForm (PObjHas(ds,k,(hs,cs),l))));
  let ps = List.map (fun d -> embedHas d [k]) ds in
  if l = lRoot then
    pOr ps
  else
    pOr (ps @ [PHeapHas ((hs,[]), l, k)])

let ohCache = Hashtbl.create 17

(* this version caches and also prints results of top-level query *)
let embedObjHas ds k h l =
  if Hashtbl.mem ohCache (ds,k,h,l) then Hashtbl.find ohCache (ds,k,h,l)
  else begin
    let p = embedObjHas ds k h l in
    printUnroll "embed" (PObjHas(ds,k,h,l)) p;
    Hashtbl.add ohCache (ds,k,h,l) p;
    p
  end

(***** embed WObjSel *****)

let createContextOS p =
  let table = Id.create () in (* track all the different wobjsels *)
  let fWal = function
    | WObjSel(os) -> wHole (Id.process table os)
    | w           -> w in
  let q = mapForm ~fWal ~onlyTopForm:true p in
  let n = Id.size table in
  let objsels = List.map (fun i -> (i, Id.getVal table i)) (Utils.list1N n) in
  (q, objsels)

let applyContextOS ctx (i,(ds,k,(hs,cs),l)) =
  if cs <> [] then
    failwith (spr "embedObjSel: constraints should've been expanded:\n\n%s"
      (strWal (WObjSel(ds,k,(hs,cs),l))));
  let rec foo = function
    | [] ->
        let subst = ([sHole i, WHeapSel ((hs,[]), l, k)], [], [], []) in
        substForm subst ctx
    | d::ds ->
        let subst = ([sHole i, sel d k], [], [], []) in
        pAnd [pImp (embedHas d [k]) (substForm subst ctx);
              pImp (pNot (embedHas d [k])) (foo ds)]
  in
  foo ds

let osCache = Hashtbl.create 17

let embedObjSels p =
  if Hashtbl.mem osCache p then Hashtbl.find osCache p
  else begin
    let (ctx,objsels) = createContextOS p in
    let q = List.fold_left applyContextOS ctx objsels in
    if p <> q then printUnroll "embed" p q;
    Hashtbl.add osCache p q;
    q
  end

let embedObjSelsInsideOut p =
  if Hashtbl.mem osCache p then Hashtbl.find osCache p
  else begin
    let q = mapForm ~fForm:embedObjSels ~onlyTopForm:true p in
    if p <> q then printUnroll "inside out embed" p q;
    Hashtbl.add osCache p q;
    q
  end

(***** entry point *****)

(*
(* not using mapForm, since want to recurse inside only formulas *)
let rec embedForm1 p =
  match p with
    | PEq _ | PApp _ | PTru | PFls | PUn _ | PHeapHas _ -> p
    | PConn(f,ps)       -> PConn (f, List.map embedForm1 ps)
    | PHas(d,ks)        -> embedHas d ks
    | PDomEq(d,ks)      -> embedDomEq d ks
    | PEqMod(d1,d2,ks)  -> embedEqMod d1 d2 ks
    | PObjHas(ds,k,h,l) -> embedObjHas ds k h l
    | PAll _ -> failwith "embedForm1: PAll shouldn't appear before expansion"
*)
let embedForm1 p =
  let fForm = function
    | PHas(d,ks)        -> embedHas d ks
    | PDomEq(d,ks)      -> embedDomEq d ks
    | PEqMod(d1,d2,ks)  -> embedEqMod d1 d2 ks
    | PObjHas(ds,k,h,l) -> embedObjHas ds k h l
    | p                 -> p
  in
  mapForm ~fForm ~onlyTopForm:true p

let embedForm p = p |> embedForm1 |> embedObjSelsInsideOut |> formToSMT


(***** More stuff *************************************************************)

let tyArrayTuple tInv ts extensible = 
  let p = if extensible then ge else eq in
  failwith "tyArrayTuple: use QArray and move up in file"
(*
  let ps =
    packed theV :: p (arrlen theV) (wInt (List.length ts))
    :: Utils.map_i (fun ti i -> applyTyp ti (sel theV (wInt i))) ts in
  THasTyp ([UArray tInv], pAnd ps)
*)

