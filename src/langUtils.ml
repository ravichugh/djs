
open Lang

module Id = Utils.IdTable


(* let pr = Printf.printf    use Log.log instead! *)
let spr = Printf.sprintf
let fpr = Printf.fprintf

let (|>) f x = x f

let maybeApply f = function
  | Some(x) -> Some (f x)
  | None    -> None


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

let freshVarX =
  let counters = Hashtbl.create 17 in
  fun x ->
    let c = if Hashtbl.mem counters x then Hashtbl.find counters x else 0 in
    Hashtbl.replace counters x (succ c);
    spr "%s__%04d" x (succ c)


(***** Map ********************************************************************)

let mapTyp ?(fTyp  = fun x -> x)
           ?(fForm = fun x -> x)
           ?(fTT   = fun x -> x)
           ?(fWal  = fun x -> x)
           ?(fVal  = fun x -> x) 
           ?(fLoc  = fun x -> x)
           ?(onlyTopForm=false)
           t =

  let rec fooTyp = function
    | TRefinement(x,p)   -> fTyp (TRefinement (x, fooForm p))
    | TQuick(x,qt,p)     -> fTyp (TQuick (x, fooQuickTyp qt, fooForm p))
    | TBaseUnion(l)      -> fTyp (TBaseUnion l)
    | TMaybeNullRef(l,p) -> fTyp (TMaybeNullRef (fLoc l, fooForm p))
    | TNonNullRef(l)     -> fTyp (TNonNullRef (fLoc l))
    | TMaybeUndef(t,p)   -> fTyp (TMaybeUndef (fooTyp t, fooForm p))

  (* and fooPrenexTyp = function *)
  (*   | TExists _          -> failwith "mapTyp TExists" *)

  and fooQuickTyp = function
    | QBase(bt)   -> QBase bt
    | QRecd(l,b)  -> QRecd (List.map (fun (f,t) -> (f, fooTyp t)) l, b)
    | QTuple(l,b) -> QTuple (List.map (fun (f,t) -> (f, fooTyp t)) l, b)
    | QBoxes(l)   -> QBoxes (List.map fooTT l)

  and fooForm = function
    | PEq(w1,w2)         -> fForm (PEq (fooWal w1, fooWal w2))
    | PApp(s,ws)         -> fForm (PApp (s, List.map fooWal ws))
    | PHasTyp(w,u)       -> fForm (PHasTyp (fooWal w, fooTT u))
    | PHeapHas(h,l,w)    -> fForm (PHeapHas (fooHeap h, fLoc l, fooWal w))
    | PConn(s,ps)        -> fForm (PConn (s, List.map fooForm ps))
    | PHas(w,ws)         -> fForm (PHas (fooWal w, List.map fooWal ws))
    | PDomEq(w,ws)       -> fForm (PDomEq (fooWal w, List.map fooWal ws))
    | PEqMod(w1,w2,ws)   -> let ws = List.map fooWal ws in
                            fForm (PEqMod (fooWal w1, fooWal w2, ws))
    | PObjHas(ds,k,h,l)  -> let ds = List.map fooWal ds in
                            fForm (PObjHas (ds, fooWal k, fooHeap h, fLoc l))
    | PAll(x,p)          -> fForm (PAll (x, fooForm p))
    (* | PAll _             -> failwith "mapForm: PAll shouldn't appear" *)

  and fooTT = function
    | UNull     -> fTT UNull
    | UVar(x)   -> fTT (UVar x)
    | URef(l)   -> fTT (URef (fLoc l))
    | UMacro(x) -> fTT (UMacro x)
    | UArray(t) ->
        if onlyTopForm then fTT (UArray t)
        else fTT (UArray (fooTyp t))
    | UArrow(l,x,t1,h1,t2,h2) as u ->
        if onlyTopForm then fTT u
        else let (t1,h1) = fooTyp t1, fooHeap h1 in
             let (t2,h2) = fooTyp t2, fooHeap h2 in
             fTT (UArrow (l, x, t1, h1, t2, h2))

  and fooWal = function
    | WVal(v)         -> fWal (WVal (fooVal v))
    | WApp(s,ws)      -> fWal (WApp (s, List.map fooWal ws))
    | WBot            -> fWal WBot
    | WHeapSel(h,l,w) -> fWal (WHeapSel (fooHeap h, fLoc l, fooWal w))
    | WObjSel(ds,k,h,l) ->
        let ds = List.map fooWal ds in
        fWal (WObjSel (ds, fooWal k, fooHeap h, fLoc l))

  (* TODO if var elim does not end up using this, might get rid of it *)
  and fooVal v = { v with value = match v.value with
    | VExtend(v1,v2,v3) -> fVal (VExtend (fooVal v1, fooVal v2, fooVal v3))
    | v                 -> fVal v
  }

  (* not doing anything with heap vars *)
  and fooHeap (hs,cs) =
    let cs =
      List.map (function
        | (l,HStrong(x,s,lo,ci)) ->
            let ci = maybeApply fooTyp ci in
            (fLoc l, HStrong (x, fooTyp s, maybeApply fLoc lo, ci))
        | (l,HWeak(tok)) ->
            (fLoc l, HWeak tok)
      ) cs
    in
    (hs, cs)

  in fooTyp t

let mapForm ?(fForm = fun x -> x)
            ?(fTT   = fun x -> x)
            ?(fWal  = fun x -> x)
            ?(fVal  = fun x -> x)
            ?(fLoc  = fun x -> x)
            ?(onlyTopForm=false)
            f =
  let t = TRefinement ("dummyMapForm", f) in
  match mapTyp ~fForm ~fTT ~fWal ~fVal ~fLoc ~onlyTopForm t with
    | TRefinement("dummyMapForm",f') -> f'
    | _ -> failwith "mapForm: should never fail"

let mapHeap ?(fForm = fun x -> x)
            ?(fWal  = fun x -> x)
            ?(fLoc  = fun x -> x)
            h =
  let p = PHeapHas (h, LocConst "dummyMapHeap", WBot) in
  match mapForm ~fForm ~fWal ~fLoc p with
    | PHeapHas(h',_,_) -> h'
    | _ -> failwith "mapHeap: impossible"


(***** Fold *******************************************************************)

(* gives the client access to all formulas, walues, and type terms *)

let foldTyp ?(fForm = fun acc _ -> acc)
            ?(fTT   = fun acc _ -> acc)
            ?(fWal  = fun acc _ -> acc) (init: 'a) (t: typ) : 'a =

  let rec fooTyp acc = function
    | TRefinement(_,p)   -> fooForm acc p
    | TQuick(_,qt,p)     -> fooForm (fooQuickTyp acc qt) p
    | TBaseUnion _       -> acc
    | TNonNullRef(l)     -> fTT acc (URef l) (* a bit hacky to rely on fTT *)
    | TMaybeNullRef(l,p) -> fooForm (fTT acc (URef l)) p
    | TMaybeUndef(t,p)   -> fooForm (fooTyp acc t) p

  (* and fooPrenexTyp acc = function *)
  (*   | TExists _          -> failwith "foldTyp TExists" *)

  and fooQuickTyp acc = function
    | QBase _            -> acc
    | QBoxes(us)         -> List.fold_left fooTT acc us
    | QRecd(l,_)         -> List.fold_left fooTyp acc (List.map snd l)
    | QTuple(l,_)        -> List.fold_left fooTyp acc (List.map snd l)

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
    | UMacro(x)     -> fTT acc (UMacro x)
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
      | (_,HStrong(_,s,_,_)) -> fooTyp acc s
      | (_,HWeak(_)) -> acc
    ) acc cs

  in fooTyp init t


(***** Map Exp ****************************************************************)

let mapExp fE e =
  let rec fooExp = function
    | EVal(v) -> fE (EVal (fooVal v))
    | EDict(es) ->
        fE (EDict (List.map (fun (e1,e2) -> (fooExp e1, fooExp e2)) es))
    | EArray(t,es) -> fE (EArray (t, List.map fooExp es))
    | ETuple(es) -> ETuple (List.map fooExp es)
    | EIf(e1,e2,e3) -> fE (EIf (fooExp e1, fooExp e2, fooExp e3))
    | EApp(poly,e1,e2) -> fE (EApp (poly, fooExp e1, fooExp e2))
    | ELet(x,fo,e1,e2) -> fE (ELet (x, fo, fooExp e1, fooExp e2))
    | EExtern(x,t,e) -> fE (EExtern (x, t, fooExp e))
    | EHeapEnv(l,e) -> fE (EHeapEnv (l, fooExp e)) (* if needed, add fold l *)
    | EMacro(x,m,e) -> fE (EMacro (x, m, fooExp e))
    | ETcFail(s,e) -> fE (ETcFail (s, fooExp e))
    | EAsW(e,w) -> fE (EAsW (fooExp e, w))
    | ENewref(l,e,ci) -> fE (ENewref (l, fooExp e, ci))
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
    | ENewObj(e1,l1,e2,l2,ci) -> fE (ENewObj (fooExp e1, l1, fooExp e2, l2, ci))
    | ELoadSrc(s,e) -> fE (ELoadSrc (s, fooExp e))
    | ELoadedSrc(s,e) -> fE (ELoadedSrc (s, fooExp e))
  and fooVal v = { v with value = match v.value with
    | VBase(bv) -> VBase bv
    | VNull -> VNull
    | VVar(x) -> VVar x
    | VEmpty -> VEmpty
    (* | VNewObjRef(i) -> VNewObjRef i *)
    | VExtend(v1,v2,v3) -> VExtend (fooVal v1, fooVal v2, fooVal v3)
    | VArray(t,vs) -> VArray (t, List.map fooVal vs)
    | VTuple(vs) -> VTuple (List.map fooVal vs)
    | VFun(x,e) -> VFun (x, fooExp e)
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
    | EIf(e1,e2,e3) -> fE (List.fold_left fooExp acc [e1;e2;e3]) exp
    | EApp(poly,e1,e2) -> fE (List.fold_left fooExp acc [e1;e2]) exp
    | ELet(x,fo,e1,e2) -> fE (List.fold_left fooExp acc [e1;e2]) exp
    | EExtern(x,t,e) -> fE (fooExp acc e) exp
    | EHeapEnv(l,e) -> fE (fooExp acc e) exp (* if needed, add fold l *)
    | EMacro(x,m,e) -> fE (fooExp acc e) exp
    | ETcFail(s,e) -> fE (fooExp acc e) exp
    | EAsW(e,w) -> fE (fooExp acc e) exp
    | ENewref(l,e,ci) -> fE (fooExp acc e) exp
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
    | ENewObj(e1,l1,e2,l2,ci) -> fE (List.fold_left fooExp acc [e1;e2]) exp
    | ELoadSrc(s,e) -> fE (fooExp acc e) exp
    | ELoadedSrc(s,e) -> fE (fooExp acc e) exp
  and fooVal acc v = match v.value with
    | VBase(bv) -> fV acc v.value
    | VNull -> fV acc v.value
    | VVar(x) -> fV acc v.value
    | VEmpty -> fV acc v.value
    (* | VNewObjRef(i) -> fV acc v.value *)
    | VExtend(v1,v2,v3) -> fV (List.fold_left fooVal acc [v1;v2;v3]) v.value
    | VArray(t,vs) -> fV (List.fold_left fooVal acc vs) v.value
    | VTuple(vs) -> fV (List.fold_left fooVal acc vs) v.value
    | VFun(x,e) -> fV (fooExp acc e) v.value
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
let vTup xs       = {pos = pos0; value = VTuple xs}
(* let vNewObjRef i  = {pos = pos0; value = VNewObjRef i} *)
let vFun (p,e)    = {pos = pos0; value = VFun (p, e)}
let eFun (p,e)    = EVal (vFun (p,e))

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

let mkAppUn vFun vArgs =
  EApp (([],[],[]), EVal vFun, EVal (wrapVal pos0 (VTuple vArgs)))

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
let pNonNull w    = pNot (eq w wNull)
let pIsBang w u   = pAnd [hastyp w u; pNonNull w]

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

let tyUndef       = TQuick ("v", QBase BUndef, pTru) (* ty (eq theV wUndef) *)
let tyNotUndef    = ty (pNot (eq theV wUndef))

let tyTypTerm = function
  | URef(l) -> tyRef l (* so that default for references can be tweaked *)
  | u       -> TQuick ("v", QBoxes [u], pTru)

let tyTupleNone l = (* no component has a binder *)
  TQuick ("v", QTuple (List.map (fun t -> (None, t)) l, false), pTru)

let tyTupleSome l = (* some components have binders *)
  TQuick ("v", QTuple (List.map (fun (xo,t) -> (xo, t)) l, false), pTru)

let tyTupleAll l = (* all components have binders *)
  TQuick ("v", QTuple (List.map (fun (x,t) -> (Some x, t)) l, false), pTru)


(* setting the default for array tuple invariants to be v != undefined,
   not Top, so that packed array accesses can at least prove that the
   value retrieved is not undefined *)
let tyArrDefault = tyNotUndef

let bindersOfDepTuple l =
  List.fold_left (fun acc -> function Some(x) -> x::acc | None -> acc)
    [] (List.map fst l)

(* maybeValOfSingleton used by TcDref3 and Sub to manipulate heap bindings with
   singleton types. can make maybeValOfWal better by "evaluating" record walues
   to values *)

(* TODO might phase this out for HSing *)

let rec maybeValOfWal = function
  | WVal(v) -> Some v
  | _ -> None

let valToSingleton v = ty (PEq (theV, WVal v))

let maybeValOfSingleton = function
  (* | TRefinement("v",PEq(WVal({value=VVar"v"}),w)) -> maybeValOfWal w *)
  | TRefinement(x,PEq(WVal({value=VVar(x')}),w)) when x = x' -> maybeValOfWal w
  | _ -> None


(***** Id Tables **************************************************************)

let oc_boxes = open_out (Settings.out_dir ^ "boxes.txt")

(***** Strings *****)

let idStrings = Id.create ()

let getStringId s = (* assigning ids on demand *)
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


(***** DJS native prototypes **************************************************)

let frozenNatives =
  let foo l v l' = (l, HStrong (None, valToSingleton v, Some l', None)) in
  [ foo lRoot vNull lRoot
  ; foo lObjPro (vVar "theObjPro") lRoot
  ; foo lArrPro (vVar "theArrPro") lObjPro
  ; foo lFunPro (vVar "theFunPro") lObjPro ]

let filterNatives cs =
  List.filter (fun (l,hc) -> not (List.mem (l,hc) frozenNatives)) cs


(***** Printing to SMT-LIB-2 format and stdout ********************************)

let pretty = ref true

let simpleSugarToTyp = [
  ("Top"         , tyAny          );
  (* ("Bot"         , tyFls          ); *)
  ("Dict"        , tyDict         );
  ("Num"         , tyNum          );
  ("Int"         , tyInt          );
  ("Bool"        , tyBool         );
  ("Str"         , tyStr          );
  ("Empty"       , tyEmpty        );
  ("Undef"       , tyUndef        );
  ("NotUndef"    , tyNotUndef     );
  ("IntOrBool"   , tyIntOrBool    );
  ("IntOrStr"    , tyIntOrStr     );
  ("NumOrBool"   , tyNumOrBool    );
  (* ("NonNegInt"   , ty (pAnd [pInt; ge theV (wInt 0)])); *)
]

let simpleSugarOfTyp =
  List.fold_left (fun acc (s,t) -> (t,s)::acc) [] simpleSugarToTyp

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
    | Bool(b), true  -> spr "%b" b
    | Bool(b), false -> if b then "VTrue" else "VFalse"
    | Undef, _       -> "undefined"
    | Int(i), true   -> spr "%d" i
    | Int(i), false  -> spr "(VInt %d)" i
    | Str(s), true   -> spr "\"%s\"" s
    | Str(s), false  -> spr "(VStr %d)" (getStringId s)

let rec strVal v = match v.value with
  | VBase(c)    -> strBaseValue c
  | VNull       -> "null"
  | VVar(x)     -> x
  | VEmpty      -> "empty"
  (* | VNewObjRef(i) -> spr "(VObjRef %d)" i *)
  | VFun _ as v -> spr "(VFun %d)" (Id.process idLamTerms v)
  | VExtend(v1,v2,v3) ->
      if !pretty
      then spr "(%s with %s = %s)" (strVal v1) (strVal v2) (strVal v3)
      else spr "(upd %s %s %s)" (strVal v1) (strVal v2) (strVal v3)
  | VArray(_,vs) ->
      if !pretty
      then spr "<%s> as Arr(_)" (String.concat " " (List.map strVal vs))
      else failwith "strVal VArray: should have been expanded by embedForm"
  | VTuple(vs) ->
      if !pretty
      then spr "(%s)" (String.concat ", " (List.map strVal vs))
      else failwith "strVal VTuple: should have been expanded by embedForm"

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

let strLocBinds l =
  (* spr "%s |->" (strLoc l) *)
  spr "%s:" (strLoc l)

let strProtoLocOpt = function
  | Some(l) -> spr " > %s" (strLoc l)
  | None    -> ""

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
  | t when List.mem_assoc t simpleSugarOfTyp -> List.assoc t simpleSugarOfTyp
  | TRefinement("v",p)   -> spr "{%s}" (strForm p)
  | TRefinement(x,p)     -> spr "{%s|%s}" x (strForm p)
  | TQuick(x,qt,p)       -> strTQuick x qt p
  | TBaseUnion(l)        -> String.concat "Or" (List.map strBaseTyp l)
  | TNonNullRef(l)       -> spr "Ref(%s!)" (strLoc l)
  | TMaybeNullRef(l,p)   -> if !Settings.printShortQuick && p = pTru
                            then spr "Ref(%s?)" (strLoc l)
                            else spr "{Ref(%s?)|%s}" (strLoc l) (strForm p)
  | TMaybeUndef(t,p)     -> spr "{?(%s)|%s}" (strTyp t) (strForm p)

and strPrenexTyp = function
  | TExists(x,t,s) -> spr "exists (%s:%s). %s" x (strTyp t) (strPrenexTyp s)
  | Typ(t)         -> strTyp t

and strTQuick x qt p =
  match (!Settings.printShortQuick, x, qt, p) with
    | _,    _, QBoxes([]), _     -> failwith "strTyp: weird type with QBoxes []"
    (* these three cases omit the refinement formula *)
    | true, _, QRecd(l,true), _  -> strQuickTyp (QRecd (l, true))
    | true, _, QTuple(l,true), _ -> strQuickTyp (QTuple (l, true))
    | true, _, QBoxes([u]), _    -> strTT u
    (* otherwise, omit the formula only if it's pTru *)
    | _,    _, QBoxes([u]), p when p = pTru -> strTT u
    | _,    _, QBase(_), p 
    | _,    _, QRecd(_), p 
    | _,    _, QTuple(_), p when p = pTru -> strQuickTyp qt
    | _,  "v", _, _ -> spr "{%s|%s}" (strQuickTyp qt) (strForm p)
    | _             -> spr "{%s:%s|%s}" x (strQuickTyp qt) (strForm p)

and strQuickTyp = function
  | QBase(bt) -> strBaseTyp bt
  | QRecd(l,b) ->
      spr "{%s%s}"
        (String.concat ", "
          (List.map (fun (f,t) -> spr "%s:%s" f (strTyp t)) l))
        (if b then ", _:Bot" else "")
  (* TODO: parser currently doesn't accept QBoxes for more than one box
     or QTuple. if and when i need to add these to the parser, update these
     to match. *)
  | QBoxes(us) -> String.concat " +++++ " (List.map strTT us)
  | QTuple(l,b) -> spr "[%s%s]" (strDepTuple l) (if b then "; exact" else "")

and strDepTuple l =
  String.concat ", "
    (List.map (function (Some(x),t) -> spr "%s:%s" x (strTyp t)
                      | (None   ,t) -> strTyp t) l)

and strTT = function
  | UMacro(x) -> x
  | UVar(x)   -> x
  | UNull     -> "Null"
  | URef(l)   -> spr "Ref(%s)" (strLoc l)
  | UArray(t) -> spr "Arr(%s)" (strTyp t)
  | UArrow(polyArgs,x,t1,e1,t2,e2) -> begin
      (* following the parser, assuming that if t1 = (x1:T1, ...),
         then the binder is trivial. *)
      let strDom =
        match t1 with
          | TQuick(_,QTuple(l,false),_) -> spr "(%s)" (strDepTuple l)
          | _                           -> spr "%s:%s" x (strTyp t1) in
      match polyArgs, e1, e2 with
        (* can only omit h if it doesn't appear in any types
        | (ts,ls,[h]), ([h1],cs1), ([h2],cs2) when h = h1 && h = h2 ->
            let s0 =
              match ts,ls with
                | [],[] -> ""
                | ts,ls -> spr "[%s;%s] " (strStrs ts) (strStrs ls) in
            let se1 = if cs1 = [] then "" else spr " / (%s)" (strHeapBindings cs1) in
            let se2 = if cs2 = [] then "" else spr " / (%s)" (strHeapBindings cs2) in
            spr "%s%s%s -> %s%s" s0 strDom se1 (strTyp t2) se2
        *)
        | (ts,ls,hs), _, _ ->
            let s0 = spr "[%s;%s;%s] " (strStrs ts) (strStrs ls) (strStrs hs) in
            let se1 = spr " / %s" (strHeap e1) in
            let se2 = spr " / %s" (strHeap ~arrowOutHeap:true e2) in
            spr "%s%s%s -> %s%s" s0 strDom se1 (strTyp t2) se2
    end

and strForm = function
  | p when p = pTru -> if !pretty then "TRU" else "true"
  | p when p = pFls -> if !pretty then "FLS" else "false"
  | PEq(w1,w2)      -> spr "(= %s %s)" (strWal w1) (strWal w2)
  | PApp(s,ws)      -> spr "(%s %s)" (strPredSym s)
                         (String.concat " " (List.map strWal ws))
  | PConn(s,l)      -> strFormExpanded s l
  | PAll(x,p)       -> spr "(forall ((%s DVal)) %s)" x (strForm p)
  (* TODO 8/30/12 once registerBox keeps boxes in sync with logical context,
     can assert these axioms once per box rather than here *)
  | PHasTyp(w,(URef(l) as u)) when isStrongLoc l ->
      let sNull = strVal vNull in
      if !pretty then
        let sU = strTT u in
        spr "(and (%s :: %s) (not (%s :: %s)))" (strWal w) sU sNull sU
      else
        let i = registerBox u in
        spr "(and (hastyp %s %d) (not (hastyp %s %d)))" (strWal w) i sNull i
  (* TODO make the call to registerBox somewhere more appropriate. *)
  | PHasTyp(w,u) ->
      if !pretty
        then spr "(%s :: %s)" (strWal w) (strTT u)
        else spr "(hastyp %s %d)" (strWal w) (registerBox u)
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
  | HWeak(ts) -> strThawState ts
  | HStrong(xo,s,lo,ci) ->
      spr "%s%s%s%s"
        (match xo with Some(x) -> spr "%s:" x | None -> "")
        (strTyp s)
        (match ci with Some(t) -> spr " [%s]" (strTyp t) | None -> "")
        (strProtoLocOpt lo)

and strHeapBinding (l,hc) = spr "%s %s" (strLocBinds l) (strHeapCell hc)

and strHeapBindings cs =
  if not !Settings.augmentHeaps then
    String.concat ", " (List.map strHeapBinding cs)
  else
    let (sNatives,cs) =
      if List.for_all (fun (l,hc) ->
           List.mem_assoc l cs && List.assoc l cs = hc
         ) frozenNatives
      then (["natives"], filterNatives cs)
      else ([], cs)
    in
    spr "%s" (String.concat ", " (sNatives @ List.map strHeapBinding cs))

and strHeap ?(arrowOutHeap=false) (hs,cs) =
  (* let cs = filterNatives cs in *)
  match hs, cs with
    | [h], [] when arrowOutHeap -> spr "(%s)" h (* parens to avoid conflict *)
    | [h], [] -> h
    | [h], _  -> spr "%s + (%s)" h (strHeapBindings cs)
    | [] , [] -> "" (* TODO would be nice to get rid of this case *)
    | [] , _  -> failwith "strHeap: zero heap vars? and bindings"
    | _  , _  -> failwith (spr "strHeap: multiple vars [%s]" (strStrs hs))

and strWeakLoc (m,t,l) =
  spr "(%s %s > %s)" (strLocBinds m) (strTyp t) (strLoc l)

and strWorld (s,h) =
  spr "%s / %s" (strTyp s) (strHeap h)

let strFrame (l,h,w) =
  spr "[%s] %s -> %s" (String.concat "," l) (strHeap h) (strWorld w)

let strCloInv = function
  | Some(t) -> spr " %s" (strTyp t)
  | None    -> ""

let strBinding (x,s) = spr "%s:%s" x (strTyp s)

let strHeapEnvCell = function
  | HEWeak(ts) -> strThawState ts
  | HEStrong(v,lo,ci) ->
      spr "%s%s%s" (strVal v) (strProtoLocOpt lo) (strCloInv ci)

let strHeapEnvBinding (l,hc) = spr "%s %s" (strLocBinds l) (strHeapEnvCell hc)

let strHeapEnv (hs,cs) =
  let s = String.concat ", " (List.map strHeapEnvBinding cs) in
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

(* module VVars = Set.Make (struct type t = vvar let compare = compare end) *)
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
    | TQuick(_,QTuple(l,_),_) -> bindersOfDepTuple l
    | _ -> acc
  in foo [] t

let heapBinders (_,cs) =
  List.fold_left
    (fun acc (l,hc) ->
       match hc with HWeak _ -> acc
                   | HStrong(None,_,_,_) -> acc
                   | HStrong(Some(x),_,_,_) -> x::acc) [] cs

(* all the freeVarsX functions are of the form env:Quad.t -> x:X -> Quad.t *)

let rec freeVarsVal env v = match v.value with
  | VVar(x) -> if Quad.memV x env then Quad.empty else Quad.addV x Quad.empty
  | VBase _ | VNull | VEmpty (* | VNewObjRef _ *) -> Quad.empty
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
  | TRefinement(x,p)   -> freeVarsForm (Quad.addV x env) p
  | TBaseUnion _       -> Quad.empty
  | TQuick(x,qt,p)     -> let v1 = freeVarsForm env p in
                          let v2 = freeVarsQuickTyp env qt in
                          Quad.combineList [v1;v2]
  | TNonNullRef(l)     -> freeVarsLoc env l
  | TMaybeNullRef(l,p) -> let v1 = freeVarsLoc env l in
                          let v2 = freeVarsForm env p in
                          Quad.combineList [v1;v2]
  | TMaybeUndef(t,p) ->
      Quad.combineList [freeVarsTyp env t; freeVarsForm env p]

and freeVarsPrenexTyp env = function
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
  | UMacro(x) -> failwith (spr "freeVarsTT macro [%s]: should be expanded" x)
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
    | (l,HStrong(_,t,_,_)) ->
         Quad.combineList [freeVarsLoc env l; freeVarsTyp env t; acc]
    | (l,HWeak(_)) ->
         freeVarsLoc env l
  ) free cs

and freeVarsWorld env (t,h) =
  let xs = heapBinders h in
  let env' = List.fold_left (fun env x -> Quad.addV x env) env xs in
  Quad.combine (freeVarsHeap env h) (freeVarsTyp env' t)

and freeVarsLoc env = function
  | LocVar(x)  -> if Quad.memL x env then Quad.empty else Quad.addL x Quad.empty
  | LocConst _ -> Quad.empty

let rec bindersOfPat = function
  | PLeaf(x) -> VVars.singleton x
  | PNode(l) -> List.fold_left VVars.union VVars.empty (List.map bindersOfPat l)

let rec freeVarsExp env = function
  | EVal(v) -> freeVarsVal env v
  | EDict(l) ->
      List.fold_left VVars.union VVars.empty
        (List.map (fun (e1,e2) ->
           VVars.union (freeVarsExp env e1) (freeVarsExp env e2)) l)
  | EArray(_,es) | ETuple(es) -> freeVarsExpList env es
  | EIf(e1,e2,e3) -> freeVarsExpList env [e1;e2;e3]
  | EApp(_,e1,e2) | ESetref(e1,e2) | ENewObj(e1,_,e2,_,_) ->
      freeVarsExpList env [e1;e2]
  | ELet(x,_,e1,e2) ->
      VVars.union (freeVarsExp env e1) (freeVarsExp (VVars.add x env) e2)
  | EExtern(x,_,e) -> freeVarsExp (VVars.add x env) e
  | ELabel(_,e) | EBreak(_,e) | ENewref(_,e,_) | EDeref(e)
  | EFreeze(_,_,e) | EThaw(_,e) | EWeak(_,e) | EHeapEnv(_,e)
  | EMacro(_,_,e) | ETcFail(_,e) | EAsW(e,_) ->
      freeVarsExp env e
  | ELoadSrc _ | ELoadedSrc _ -> failwith "freeVarsExp eload"
  | EThrow _ | ETryCatch _ | ETryFinally _ -> failwith "freeVarsExp exception"

and freeVarsExpList env es =
  List.fold_left VVars.union VVars.empty (List.map (freeVarsExp env) es)

and freeVarsVal env v = match v.value with
  | VBase _ | VNull | VEmpty -> VVars.empty
  | VVar(x) -> if VVars.mem x env then VVars.empty else VVars.singleton x
  | VFun(p,e) -> freeVarsExp (VVars.union env (bindersOfPat p)) e
  | VExtend(v1,v2,v3) -> freeVarsValList env [v1;v2;v3]
  | VArray(_,vs) | VTuple(vs) -> freeVarsValList env vs

and freeVarsValList env vs =
  List.fold_left VVars.union VVars.empty (List.map (freeVarsVal env) vs)

let freeVarsExp e = freeVarsExp VVars.empty e


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
      (* | VNewObjRef _  -> WVal v *)
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
  | TBaseUnion(l) -> TBaseUnion l
  | TNonNullRef(l) -> TNonNullRef (substLoc subst l)
  | TMaybeNullRef(l,p) -> TMaybeNullRef (substLoc subst l, substForm subst p)
  | TMaybeUndef(t,p) -> TMaybeUndef (substTyp subst t, substForm subst p)
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

and substPrenexTyp subst = function
  | Typ(t) -> Typ (substTyp subst t)
  | TExists(x,t1,t2) ->
      let (l,_,_,_) = subst in
      if List.mem_assoc x l then failwith "subst TExists" (* TODO 8/20 *)
      else TExists (x, substTyp subst t1, substPrenexTyp subst t2)

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
  | UMacro(x) -> UMacro x
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
      | (l,HStrong(xo,s,lo,ci)) ->
          let ci = maybeApply (substTyp subst) ci in
          (* ci can refer to x, so do the substitution before removing x *)
          let subst =
            match xo with
              | None -> subst
              | Some(x) -> MasterSubst.removeVVars [x] subst in
          let hc = HStrong (xo, substTyp subst s, substLocOpt subst lo, ci) in
          (substLoc subst l, hc)
      | (l,HWeak(Frzn)) ->
          (substLoc subst l, HWeak Frzn)
      | (l,HWeak(Thwd(l'))) ->
          (substLoc subst l, HWeak (Thwd (substLoc subst l')))
    ) cs
  in
  (hs, cs)

and substLoc subst = function
  | LocConst(x) -> LocConst x
  | LocVar(x) -> (* location variable substitution *)
      let (_,_,sub,_) = subst in
      if List.mem_assoc x sub then List.assoc x sub else LocVar x

and substLocOpt subst = function
  | Some(l) -> Some (substLoc subst l)
  | None    -> None

(* [[T]](w) *)
and applyTyp t w =
  match t with
    | TBaseUnion(l)      -> pOr (List.map (fun bt -> applyBaseTyp bt w) l)
    | TRefinement(y,f)   -> substForm ([(y,w)],[],[],[]) f
    | TQuick(y,qt,f)     -> let f0 = applyQuickTyp (wVar y) qt in
                            substForm ([(y,w)],[],[],[]) (pAnd [f;f0])
    | TNonNullRef(l)     -> pAnd [hastyp w (URef l); pNot (eq w wNull)]
    | TMaybeNullRef(l,p) -> pAnd [pOr [hastyp w (URef l); eq w wNull];
                                  substForm ([("v",w)],[],[],[]) p]
    | TMaybeUndef(t,p)   -> pAnd [pOr [applyTyp t w; eq w wUndef];
                                  substForm ([("v",w)],[],[],[]) p]

and applyQuickTyp w = function
  | QBase(bt) -> applyBaseTyp bt w
  | QBoxes(us) -> pAnd (List.map (hastyp w) us)
  | QRecd(l,exactDom) ->
      let keys = List.map wStr (List.map fst l) in
      let dom = if exactDom then PDomEq (w, keys) else PHas (w, keys) in
      let ps = List.map (fun (f,t) -> applyTyp t (sel w (wStr f))) l in
      pAnd (pDict::dom::ps)
  | QTuple(l,exactDom) ->
      let subst =
        Utils.fold_left_i (fun acc (xo,_) i ->
          match xo with
            | None    -> acc
            | Some(x) -> (x, sel w (wProj i)) :: acc) [] l in
      let subst = (subst,[],[],[]) in
      let keys = List.map wProj (Utils.list0N (pred (List.length l))) in
      let dom = if exactDom then PDomEq (w, keys) else PHas (w, keys) in
      let ps =
        Utils.map_i (fun (_,t) i -> 
          substForm subst (applyTyp t (sel w (wProj i)))) l in
      pAnd (pDict::dom::ps)

and applyBaseTyp bt w =
  substForm ([("v",w)],[],[],[])
    (match bt with
       | BNum   -> pNum
       | BInt   -> pInt
       | BStr   -> pStr
       | BBool  -> pBool
       | BUndef -> eq (tag theV) (wStr tagUndef))


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
      | (_,HStrong(None,t,_,_)) ->
          (match maybeValOfSingleton t with
             | None -> failwith "freshenHeap 1"
             | Some(v) -> acc)
      | (_,HStrong(Some(x),_,_,_)) ->
          if Quad.memV x free then (x, freshVar x)::acc else acc
      | (_,HWeak _) ->
          acc
    ) [] cs
  in
  let binderSubstW = List.map (fun (x,x') -> (x, wVar x')) binderSubst in
  let subst = (binderSubstW,[],[],[]) in
  let cs =
    List.map (function
      | (l,HStrong(None,t,lo,ci)) ->
          (match maybeValOfSingleton t with
             | None -> failwith "freshenHeap 2"
             | Some(v) -> (l, HStrong (None, valToSingleton v, lo, ci)))
      | (l,HStrong(Some(x),s,lo,ci)) ->
          let x =
            if List.mem_assoc x binderSubst
            then List.assoc x binderSubst
            else x in
          let ci = maybeApply (substTyp subst) ci in
          (l, HStrong (Some x, substTyp subst s, lo, ci))
      | (l,HWeak(tok)) ->
          (l, HWeak tok)
    ) cs
  in
  (binderSubstW, (hs, cs))

and freshenDomain free x t =
  match freshenDepTuple free [(Some(x),t)] with
    | [(Some(x'),t')] -> (x', t')
    | _               -> failwith "freshenDomain: impossible"

let substTyp subst t =
  BNstats.time "LangUtils.substTyp" (substTyp subst) t


(***** Expression Substitution ************************************************)

(* needed only by the parser, when desugaring letrecs *)

let substVarInExp z x e =
  if x = z then e
  else failwith "substVarInExp: letrec using a freshvar for mono def?"


(***** Misc *******************************************************************)

let valOfSingleton cap t =
  match maybeValOfSingleton t with
    | Some(v) -> v
    | None -> failwith (spr "valOfSingleton [%s]: %s" cap (strTyp t))


(***** Expanding pre-formulas *************************************************)

let oc_unroll = open_out (Settings.out_dir ^ "unroll.txt")

let printUnroll cap p q =
  fpr oc_unroll "%s\n%s %s\n\n%s\n\n" (String.make 80 '-') cap
    (strForm p) (strForm q)

let printUnrollWal cap w1 w2 =
  fpr oc_unroll "%s\n%s %s\n\n%s\n\n" (String.make 80 '-') cap
    (strWal w1) (strWal w2)

let printUnroll_h (hs,cs) =
  fpr oc_unroll "  %s ++\n" (String.concat " ++" hs);
  List.iter (fun (l,hc) ->
    fpr oc_unroll "    %s %s\n" (strLocBinds l) (strHeapCell hc)) cs

let printUnroll_h_l_k pre_cap h l k post_cap =
  fpr oc_unroll "%s\n%s\n" (String.make 80 '-') pre_cap;
  printUnroll_h h;
  fpr oc_unroll "  %s\n  %s\n= %s\n" (strLoc l) (strWal k) post_cap

let printUnroll_ds_k_h_l pre_cap ds k h l post_cap =
  fpr oc_unroll "%s\n%s\n" (String.make 80 '-') pre_cap;
  fpr oc_unroll "  [%s]\n  %s\n"
    (String.concat "; " (List.map strWal ds)) (strWal k);
  printUnroll_h h;
  fpr oc_unroll "  %s\n\n= %s\n" (strLoc l) post_cap

let sHole i = spr "__hole__%d" i
let wHole i = wVar (sHole i)

(***** expand PHeapHas *****)

let rec expandHH (hs,cs) l k =
  let p =
    if l = lRoot then pFls
    else if not (List.mem_assoc l cs) then PHeapHas ((hs,[]), l, k)
    else begin
      match List.assoc l cs with
        | HStrong(None,t,Some(l'),_) ->
            pOr [has (WVal (valOfSingleton "expandHH" t)) k;
                 expandHH (hs,cs) l' k]
        | HStrong(Some(d),_,Some(l'),_) -> 
            pOr [has (wVar d) k; expandHH (hs,cs) l' k]
        | _ -> failwith (spr "expandHH: %s" (strLoc l))
    end
  in
  (* printUnroll "expandHH" (PHeapHas((hs,cs),l,k)) p; *)
  printUnroll_h_l_k "UnrollHeapHas" (hs,cs) l k (strForm p);
  p

(***** expand PObjHas *****)

let expandOH ds k (hs,cs) l =
  let rec foo ds l =
    if l = lRoot then PObjHas (ds, k, ([],[]), l)
    else if not (List.mem_assoc l cs) then PObjHas (ds, k, (hs,[]), l)
    else begin
      match List.assoc l cs with
        | HStrong(None,t,Some(l'),_) ->
            foo (ds @ [WVal (valOfSingleton "expandOH" t)]) l'
        | HStrong(Some(d),_,Some(l'),_) -> foo (ds @ [wVar d]) l'
        | _ -> failwith "expandOH: not conc constraint"
    end
  in
  let p = foo ds l in
  (* printUnroll "expandOH" (PObjHas(ds,k,(hs,cs),l)) p; *)
  printUnroll_ds_k_h_l "UnrollObjHas" ds k (hs,cs) l (strForm p);
  p

(***** expand WHeapSel *****)

(* trick to expand HeapSel in place, without computing formula contexts
   and applying them: convert to an ObjSel macro! *)
let expandHS (hs,cs) l k =
  let rec foo ds l =
    if l = lRoot then WObjSel (ds, k, ([],[]), l)
    else if not (List.mem_assoc l cs) then WObjSel (ds, k, (hs,[]), l)
    else begin
      match List.assoc l cs with
        | HStrong(None,t,Some(l'),_) ->
            foo (ds @ [WVal (valOfSingleton "expandHS" t)]) l'
        | HStrong(Some(d),_,Some(l'),_) -> foo (ds @ [wVar d]) l'
        | _ -> failwith "expandHS: not conc constraint"
    end
  in
  let w = foo [] l in
  (* printUnrollWal "expandHS" (WHeapSel((hs,cs),l,k)) w; *)
  printUnroll_h_l_k "UnrollHeapSel" (hs,cs) l k (strWal w);
  w

(***** expand WObjSel *****)

let expandOS ds k (hs,cs) l =
  let rec foo ds l =
    if l = lRoot then WObjSel (ds, k, ([],[]), l)
    else if not (List.mem_assoc l cs) then WObjSel (ds, k, (hs,[]), l)
    else begin
      match List.assoc l cs with
        | HStrong(None,t,Some(l'),_) ->
            foo (ds @ [WVal (valOfSingleton "expandOS" t)]) l'
        | HStrong(Some(d),_,Some(l'),_) -> foo (ds @ [wVar d]) l'
        | _ -> failwith "expandOS: not conc constraint"
    end
  in
  let w = foo ds l in
  (* printUnrollWal "expandOS" (WObjSel(ds,k,(hs,cs),l)) w; *)
  printUnroll_ds_k_h_l "UnrollObjSel" ds k (hs,cs) l (strWal w);
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
      (* assuming no heap predicates in ci *)
      | HStrong(x,s,lo,ci) -> (l, HStrong (x, expandPreTyp s, lo, ci))
      | HWeak(tok)         -> (l, HWeak tok)
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
  (* TODO 8/29/12: should i add the following case to match the way
     UnrollHeapSel and UnrollObjSel handle lRoot ?
  if hs = [] then substForm ([sHole i, wUndef],[],[],[]) ctx else *)
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

let valOfTuple vs =
  Utils.fold_left_i
    (fun d v i -> wrapVal pos0 (VExtend (d, vProj i, v))) vEmpty vs

let embedForm1 p =
  let fVal = function
    | VArray(_,vs)
    | VTuple(vs)   -> (valOfTuple vs).value
    | v            -> v
  in
  let fForm = function
    | PHas(d,ks)        -> embedHas d ks
    | PDomEq(d,ks)      -> embedDomEq d ks
    | PEqMod(d1,d2,ks)  -> embedEqMod d1 d2 ks
    | PObjHas(ds,k,h,l) -> embedObjHas ds k h l
    | p                 -> p
  in
  mapForm ~fVal ~fForm ~onlyTopForm:true p

let embedForm p = p |> embedForm1 |> embedObjSelsInsideOut |> formToSMT


(***** More stuff *************************************************************)

let tyArrayTuple (tInv,ts,extensible) = 
  let p = if extensible then ge else eq in
  let ps = (* could add pDict if needed ? *)
    packed theV :: p (arrlen theV) (wInt (List.length ts))
    :: Utils.map_i (fun ti i -> applyTyp ti (sel theV (wInt i))) ts in
  TQuick ("v", QBoxes [UArray tInv], pAnd ps)

