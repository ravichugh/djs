
open Lang

module Id = Utils.IdTable

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


(***** Misc (used to be in main.ml) *******************************************)

(* find some place better *)

let terminate () =
  flush stdout;
  exit 1

let printBig cap s =
  pr "\n%s\n%s\n\n%s\n\n" (String.make 80 '-') cap s

let printErr cap s =
  printBig cap s;
  pr "%s\n" (Utils.redString cap);
  terminate ()

let printParseErr s = printErr "PARSE ERROR!" s

let printTcErr  l = printErr "TC ERROR!" (String.concat "\n" l)


(***** Map ********************************************************************)

let mapTyp ?fForm:(fForm=(fun x -> x))
           ?fTT:(fTT=(fun x -> x))
           ?fWal:(fWal=(fun x -> x))
           ?fVal:(fVal=(fun x -> x)) 
           ?onlyTopForm:(onlyTopForm=false)
           t =

  let rec fooTyp = function
    | TRefinement(x,p)   -> TRefinement (x, fooForm p)
    | TTop               -> TTop
    | TBot               -> TBot
    | TBaseUnion(l)      -> TBaseUnion l
    | TBaseRefine(x,t,p) -> TBaseRefine (x, t, fooForm p)
    | THasTyp(u)         -> if onlyTopForm then THasTyp u
                            else THasTyp (fooTT u)
    | TTuple(l)          -> TTuple (List.map (fun (x,t) -> (x, fooTyp t)) l)
    | TNonNull(t)        -> TNonNull (fooTyp t)
    | TMaybeNull(t)      -> TMaybeNull (fooTyp t)
    | TExists _          -> failwith "mapTyp TExists"

  and fooForm = function
    | PEq(w1,w2)         -> fForm (PEq (fooWal w1, fooWal w2))
    | PApp(s,ws)         -> fForm (PApp (s, List.map fooWal ws))
    | PTru               -> fForm PTru
    | PFls               -> fForm PFls
    | PPacked(w)         -> fForm (PPacked (fooWal w))
    | PUn(HasTyp(w,u))   -> let u = if onlyTopForm then u else fooTT u in
                            fForm (PUn (HasTyp (fooWal w, u)))
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
    | UArray(t)     -> fTT (UArray t)
    | UArr(l,x,t1,h1,t2,h2) ->
        let (t1,h1) = fooTyp t1, fooHeap h1 in
        let (t2,h2) = fooTyp t2, fooHeap h2 in
        fTT (UArr (l, x, t1, h1, t2, h2))

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
  and fooVal = function
    | VExtend(v1,v2,v3) -> fVal (VExtend (fooVal v1, fooVal v2, fooVal v3))
    | v                 -> fVal v

  (* not doing anything with heap vars *)
  and fooHeap (hs,cs) =
    let cs =
      List.map (function
        | (l,HConc(x,s))       -> (l, HConc (x, fooTyp s))
        | (l,HConcObj(x,s,l')) -> (l, HConcObj (x, fooTyp s, l'))
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
    | TTop               -> acc
    | TBot               -> acc
    | TBaseUnion _       -> acc
    | TBaseRefine(x,t,p) -> fooForm acc p
    | THasTyp(u)         -> fooTT acc u
    | TTuple(l)          -> List.fold_left (fun a (x,t) -> fooTyp a t) acc l
    | TNonNull(t)        -> fooTyp acc t
    | TMaybeNull(t)      -> fooTyp acc t
    | TExists _          -> failwith "foldTyp TExists"

  and fooForm acc = function
    | PEq(w1,w2)         -> let acc = List.fold_left fooWal acc [w1;w2] in
                            fForm acc (PEq (w1, w2))
    | PApp(s,ws)         -> let acc = List.fold_left fooWal acc ws in
                            fForm acc (PApp (s, ws))
    | PTru               -> fForm acc PTru
    | PFls               -> fForm acc PFls
    | PPacked(w)         -> let acc = fooWal acc w in
                            fForm acc (PPacked w)
    | PUn(HasTyp(w,u))   -> let acc = fooWal acc w in
                            let acc = fooTT acc u in
                            fForm acc (PUn (HasTyp (w, u)))
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
    | UArr(l,x,t1,h1,t2,h2) ->
        let acc = fooTyp acc t1 in
        let acc = fooHeap acc h1 in
        let acc = fooTyp acc t2 in
        let acc = fooHeap acc h1 in
        fTT acc (UArr(l,x,t1,h1,t2,h2))

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
    ) acc cs

  in fooTyp init t

let foldForm fForm init t =
  foldTyp fForm (fun acc _ -> acc) (fun acc _ -> acc) init t

let foldTT fTT init t =
  foldTyp (fun acc _ -> acc) fTT (fun acc _ -> acc) init t


(***** Helpers for Abstract Syntax Programming ********************************)

let tag w         = WApp ("tag", [w])
let sel w1 w2     = WApp ("sel", [w1; w2])
(* let upd w1 w2 w3  = failwith "LangUtils.upd" *)
let upd w1 w2 w3  = WApp ("upd", [w1; w2; w3])

let has w1 w2     = PHas (w1, [w2])
let eqmod x y zs  = PEqMod (x, y, zs)
let hastyp w ut   = PUn (HasTyp (w, ut))

let plus w1 w2    = WApp ("my_plus", [w1; w2])
let minus w1 w2   = WApp ("my_minus", [w1; w2])

let arrlen x      = WApp ("len", [x])

let lt w1 w2      = PApp ("my_lt", [w1; w2])
let le w1 w2      = PApp ("my_le", [w1; w2])
let gt w1 w2      = PApp ("my_gt", [w1; w2])
let ge w1 w2      = PApp ("my_ge", [w1; w2])

let vBool x       = VBase (Bool x)
let vStr x        = VBase (Str x)
let vInt x        = VBase (Int x)
let vNull         = VBase (Null)
let vUndef        = VBase Undef (* VVar "undefined" *)

let eStr x        = EVal (vStr x)
let eVar x        = EVal (VVar x)
let wVar x        = WVal (VVar x)
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
let wProj i       = wStr (string_of_int i)

let pInt          = PEq (tag theV, wStr tagInt)
let pBool         = PEq (tag theV, wStr tagBool)
let pStr          = PEq (tag theV, wStr tagStr)
let pDict         = PEq (tag theV, wStr tagDict)

(*
let pExtend a1 a2 a3 a4 =
  PAnd [PEq (tag a1, aStr "Dict");
        PEq (eqmod a1 a2 a3, ATru);
        PEq (has a1 a3, ATru);
        PEq (sel a1 a3, a4)]
*)

let pGuard x b    = PEq (WVal x, WVal (vBool b))

let pAnd ps       = PConn ("and", ps)
let pOr ps        = PConn ("or", ps)
let pImp p q      = PConn ("implies", [p; q])
let pIff p q      = PConn ("iff", [p; q])
let pNot p        = PConn ("not", [p])
let pIte p q r    = pAnd [pImp p q; pImp (pNot p) r]

let ty p          = TRefinement ("v", p)
let tyAny         = TTop (* ty PTru *)
let tyFls         = TBot (* ty PFls *)
let tyInt         = ty pInt
let tyBool        = ty pBool
let tyStr         = ty pStr
let tyDict        = ty pDict

let tyEmpty       = ty (PEq (theV, WVal VEmpty))

(*
let tyIntOrBool   = ty (pOr [pInt; pBool])
let tyIntOrStr    = ty (pOr [pInt; pStr])
let tyStrOrBool   = ty (pOr [pStr; pBool])
*)
let tyIntOrBool   = TBaseUnion [tagInt; tagBool]
let tyIntOrStr    = TBaseUnion [tagInt; tagStr] 
let tyStrOrBool   = TBaseUnion [tagStr; tagBool] 

let tyArr x t t'  = ty (hastyp theV (UArr(([],[],[]),x,t,([],[]),t',([],[]))))
let tyNull        = ty (pAnd [PEq (theV, wNull); hastyp theV UNull])
let tyRef l       = ty (hastyp theV (URef l))

(*
let tyArrImp l x t h t' h'  = ty (PIs (theV, UArr(l,x,t,h,t',h')))
*)

let pIsBang a u   = pAnd [pNot (PEq (a, wNull)); hastyp a u]
let tyIsBang a u  = ty (pIsBang a u)


(***** Id Tables **************************************************************)

let oc_boxes = open_out (Settings.out_dir ^ "boxes.txt")

(***** Strings *****)

let isTag s =
  List.exists ((=) s) [tagInt; tagStr; tagBool; tagDict; tagFun]

(* TODO quick, but somewhat dangerous, way to set up tags for JavaScript
   without changing any tags of System D primitives. *)
let switchJsString = function
  | "number"  -> "Int"
  | "boolean" -> "Bool"
  | "string"  -> "Str"
  | "object"  -> "Dict"
  | s         -> s

let idStrings = Id.create ()

let getStringId s = (* assigning ids on demand *)
  let s =
    if !Settings.djsMode
      then switchJsString s
      else s in
  let b = not (Id.mem idStrings s) in
  let i = Id.process idStrings s in
  if b then fpr oc_boxes "\nstring %d\n  \"%s\"\n" i s;
  i

let _ = (* the ids for these strings need to match theory.lisp *)
  assert (1 = getStringId tagInt);
  assert (2 = getStringId tagBool);
  assert (3 = getStringId tagStr);
  assert (4 = getStringId tagDict);
  assert (5 = getStringId tagFun);
  assert (6 = getStringId "TagBot");
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


(***** Lambdas *****)

(* as long as ANFer prevents lambdas from appearing as arguments to functions
   (and binds them to variables first), then should not have to worry about
   substituting lambdas into types, and so logic should not have to worry
   about reasoning about function values. *)


(***** Printing to SMT-LIB-2 format *******************************************)

(* TODO separate SMT and pretty versions and get rid of flags *)

(* TODO make one flag *)
let prettyConst = ref false
let printFullUT = ref false
let printFlatTyp = ref false

(* TODO return current flags *)
let setPretty b =
  prettyConst := b;
  printFullUT := b;
  printFlatTyp := b

(* TODO *)
let sugarArrow = ref true

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

let strBaseValue v =
  match v, !prettyConst with
    | Bool(b), _    -> if b then "True" else "False"
    | Null, _       -> "null"
    | Undef, _      -> "undefined"
    | Int(i), true  -> spr "%d" i
    | Int(i), false -> spr "(VInt %d)" i
    | Str(s), true  -> spr "\"%s\""
                         (if !Settings.djsMode then switchJsString s else s)
    | Str(s), false -> spr "(VStr %d)" (getStringId s)

let rec strValue = function
  | VBase(c)    -> strBaseValue c
  | VVar(x)     -> x
  | VEmpty      -> "empty"
  | VFun _ as v -> spr "(VFun %d)" (Id.process idLamTerms v)
  | VExtend(v1,v2,v3) ->
      (* spr "(VExtend %s %s %s)" (strValue v1) (strValue v2) (strValue v3) *)
      (* spr "(upd %s %s %s)" (strValue v1) (strValue v2) (strValue v3) *)
      if !prettyConst then
        spr "(%s with %s = %s)" (strValue v1) (strValue v2) (strValue v3)
      else
        spr "(upd %s %s %s)" (strValue v1) (strValue v2) (strValue v3)
  (* TODO *)
  | VArray(_,vs) ->
      if !prettyConst then
        spr "<%s> as Arr(_)" (String.concat " " (List.map strValue vs))
      else failwith "strVal VArray"
(*
      let n = List.length vs in
      if n > 3 then err ["need to handle arbitrary arrays in theory"]
      else spr "(arr%d %s)" n (String.concat " " (List.map strValue vs))
*)

let strFunSym s =
  if !prettyConst = false then s
  else match s with
    | "my_plus" -> "+"
    | "my_minus" -> "-"
    | _ -> s

let strPredSym s =
  if !prettyConst = false then s
  else match s with
    | "my_lt" -> "<"
    | "my_le" -> "<="
    | "my_gt" -> ">"
    | "my_ge" -> ">="
    | _ -> s

let strStrs l = String.concat "," l

let rec strWalue = function
  | WVal(v) -> strValue v
  | WApp(s,ws) ->
      spr "(%s %s)" (strFunSym s) (String.concat " " (List.map strWalue ws))
  | WBot -> "bot"
  | WHeapSel((h,[]),l,k) ->
      if !prettyConst then
        spr "HeapSel(%s, %s, %s)" (strHeap (h,[])) (strLoc l) (strWalue k)
      else
        let ih = registerHeap (h,[]) in
        let il = registerLoc l in
        spr "(heapsel %d %d %s)" ih il (strWalue k)
  | WObjSel(ds,k,(h,[]),l) ->
      spr "ObjSel(%s,%s,%s,%s)"
        (strWalueList ds) (strWalue k) (strHeap (h,[])) (strLoc l)
  | WObjSel(ds,k,h,l) ->
      if !prettyConst then
        spr "ObjSel(%s,%s,%s,%s)"
          (strWalueList ds) (strWalue k) (strHeap h) (strLoc l)
      else
        let _ = setPretty true in
        printTcErr
          ["WObjSel should not have loc constraints:\n";
           spr "WObjSel(%s, %s, %s, %s)" "..."
             (strWalue k) (strLoc l) (strHeap h)]

and strWalueSet l =
  spr "{%s}" (String.concat "," (List.map strWalue l))

and strWalueList l =
  spr "[%s]" (String.concat "," (List.map strWalue l))

and strTyp = function
  | TRefinement("v",p)   -> spr "{%s}" (strForm p)
  | TRefinement(x,p)     -> spr "{%s|%s}" x (strForm p)
  | TTop                 -> "Top"
  | TBot                 -> "Bot"
  | TBaseUnion(l)        -> String.concat "Or" l
  | TBaseRefine("v",t,p) -> spr "{%s|%s}" t (strForm p)
  | TBaseRefine(x,t,p)   -> spr "{%s:%s|%s}" x t (strForm p)
  | THasTyp(u)           -> strTT u
  | TNonNull(t)          -> spr "%s" (strTyp t)
  | TMaybeNull(t)        -> spr "%s" (strTyp t)
  | TTuple(l) ->
      let l = List.map (fun (x,t) -> spr "%s:%s" x (strTyp t)) l in
      spr "[%s]" (String.concat ", " l)
  | TExists(x,t,s) ->
      spr "exists (%s:%s). %s" x (strTyp t) (strTyp s)

and strTT = function
  | UVar(x) -> x
  | URef(l) -> spr "Ref(%s)" (strLoc l)
  | UArray(t) -> spr "Arr(%s)" (strTyp t)
  | UNull   -> "Null"

  | UArr(([],[],[]),x,t1,h1,t2,h2) ->
      failwith "strTT: how can arrow have no heap vars?"

(* can't just use this to pretty print arrows without prefix var, since
   would have to check whether the var appears in the types!

  TODO do the pretty printing if h does not appear free in t1 or t2

  (* special case when single heap variable *)
  | UArr((ts,ls,[h]),x,t1,([h1],cs1),t2,([h2],cs2))
    when h = h1 && h = h2 && !sugarArrow ->
      strArrow ((ts,ls,[]),x,t1,([],cs1),t2,([],cs2))
*)

  | UArr(arr) -> strArrow arr

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
      | TTuple _ -> spr "[%s]" (strTyp t1)
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
  | PTru            -> "true"
  | PFls            -> "false"
  | PEq(w1,w2)      -> spr "(= %s %s)" (strWalue w1) (strWalue w2)
  | PApp(s,ws)      -> spr "(%s %s)" (strPredSym s)
                         (String.concat " " (List.map strWalue ws))
  | PConn("and",[]) -> spr "(true)"
  | PConn("or",[])  -> spr "(false)"
  | PConn(s,l)      -> strFormExpanded s l
  | PAll(x,p)       -> spr "(forall ((%s DVal)) %s)" x (strForm p)
  | PPacked(w)      -> spr "(packed %s)" (strWalue w)
  (* TODO make the call to registerBox somewhere more appropriate *)
  | PUn(HasTyp(w,u)) ->
      if !printFullUT
        then spr "(%s :: %s)" (strWalue w) (strTT u)
        (*else spr "(= (hastyp %s (Box %d)) true)" (strWalue w) (registerBox u)*)
        else spr "(= (hastyp %s %d) true)" (strWalue w) (registerBox u)
  | PHeapHas((h,[]),l,k) ->
      if !prettyConst then
        spr "HeapHas(%s, %s, %s)" (strHeap (h,[])) (strLoc l) (strWalue k)
      else
        let ih = registerHeap (h,[]) in
        let il = registerLoc l in
        spr "(heaphas %d %d %s)" ih il (strWalue k)
  | PHeapHas(h,l,k) ->
      if !prettyConst then 
        spr "HeapHas(%s, %s, %s)" (strHeap h) (strLoc l) (strWalue k)
      else
        let _ = setPretty true in
        printTcErr
          ["PHeapHas should not have loc constraints:\n";
           spr "HeapHas(%s, %s, %s)" (strHeap h) (strLoc l) (strWalue k)]
  (* NOTE: if one of these failwiths triggers, might be because not calling
     a prettyStr* function instead of str* *)
  | PHas(w,ws) ->
      if !printFullUT
        then spr "(has %s %s)" (strWalue w) (strWalueSet ws)
        else failwith "strForm: PHas should have been expanded"
        (* else strForm (expandPHas w ws) *)
  | PDomEq(w,ws) ->
      if !printFullUT
        then spr "(dom %s %s)" (strWalue w) (strWalueSet ws)
        else failwith "strForm: PDomEq should have been expanded"
        (* else expandPDomEq w ws *)
  | PEqMod(w1,w2,ws) ->
      if !printFullUT
        then spr "(eqmod %s %s %s)" (strWalue w1) (strWalue w2) (strWalueSet ws)
        else failwith "strForm: PEqMod should have been expanded"
        (* else expandPEqMod w1 w2 ws *)
  | PObjHas(ds,k,h,l) ->
      if !printFullUT
        then spr "ObjHas(%s,%s,%s,%s)"
               (strWalueList ds) (strWalue k) (strHeap h) (strLoc l)
        else failwith "strForm: PObjHas should have been expanded"

(* TODO reorganize options for printing *)
and strFormExpanded conn l =
  if !printFlatTyp then
    spr "(%s %s)" conn (String.concat " " (List.map strForm l))
  else begin
  incr depth;
  let s =
    l |> List.map strForm
      |> List.map (spr "%s%s" (indent()))
      |> String.concat "\n"
      |> spr "(%s\n%s)" conn in
  decr depth;
  s
  end

and registerBox ut =
  let newBox = isNewBox ut in
  let i = Id.process idTypTerms ut in
  (* if newBox then pr "new box %d\n  %s\n" i (strUnboxedTypFlat ut); *)
  setPretty true;
  if newBox then fpr oc_boxes "\nbox %d\n  %s\n" i (strTTFlat ut);
  setPretty false;
  flush oc_boxes;
  i

and registerLoc l =
  let newBox = isNewLocBox l in
  let i = Id.process idLocTerms l in
  setPretty true;
  if newBox then fpr oc_boxes "\nloc box %d\n  %s\n" i (strLoc l);
  setPretty false;
  flush oc_boxes;
  i

(* TODO really need this for just heap vars *)
and registerHeap h =
  let newBox = isNewHeapBox h in
  let i = Id.process idHeapTerms h in
  setPretty true;
  if newBox then fpr oc_boxes "\nheap box %d\n  %s\n" i (strHeap h);
  setPretty false;
  flush oc_boxes;
  i

(*
and registerBox ?ut:(ut=None) ?h:(h=None) ?l:(l=None) =
  setPretty true;
  let (i,so) =
    match uto, ho, lo with
      | Some(ut), _, _ ->
          let i = Id.process idTypTerms ut in
          let so = if isNewBox then (strUnboxedTypFlat ut) else None in
          (i, so)
      | _ -> failwith "registerBox: call with one Some arg" in
  setPretty false;
  let _ =
    match so with
      | Some(s) -> fpr oc_boxes "\nbox %d\n  %s\n" i s  
      | None -> () in
  flush oc_boxes;
  i

*)

and strTTFlat ut =
  printFullUT := true;
  let s = strTT ut in
  let s = Str.global_replace (Str.regexp "\n") " " s in
  printFullUT := false;
  s

and strHeapCell = function
  | HConc(x,s)      -> spr "%s:%s" x (strTyp s)
  | HConcObj(x,s,l) -> spr "(%s:%s, %s)" x (strTyp s) (strLoc l)

and strHeap (hs,cs) =
  let s = 
    String.concat ", " (List.map
      (fun (l,hc) -> spr "%s |-> %s" (strLoc l) (strHeapCell hc)) cs) in
  match hs, cs with
    | [], _ -> spr "[%s]" s
    (* 11/28: extra space to avoid ]] conflict *)
    | _, [] -> spr "[%s ]" (String.concat "," hs)
    | _     -> spr "[%s ++ %s ]" (String.concat "," hs) s

and strWorld (s,h) =
  spr "%s / %s" (strTyp s) (strHeap h)

let strFrame (l,h,w) =
  spr "[%s] %s -> %s" (String.concat "," l) (strHeap h) (strWorld w)

let strBinding (x,s) = spr "%s:%s" x (strTyp s)

let prettyStr f x =
  setPretty true;
  let s = f x in
  setPretty false;
  s

let prettyStrVal  = prettyStr strValue
let prettyStrWal  = prettyStr strWalue
let prettyStrForm = prettyStr strForm
let prettyStrTyp  = prettyStr strTyp
let prettyStrTT   = prettyStr strTT
let prettyStrHeap = prettyStr strHeap


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
end

let heapBinders cs =
  List.fold_left
    (fun acc (l,hc) ->
       match hc with HConc(x,_) | HConcObj(x,_,_) -> VVars.add x acc)
    VVars.empty cs

(* all the freeVarsX functions are of the form env:Quad.t -> x:X -> Quad.t *)

let rec freeVarsVal env = function
  | VBase _ -> Quad.empty
  | VVar(x) -> if Quad.memV x env then Quad.empty else Quad.addV x Quad.empty
  | VEmpty  -> Quad.empty
  | VExtend(v1,v2,v3) ->
      Quad.combineList (List.map (freeVarsVal env) [v1;v2;v3])
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
  | TTop | TBot        -> Quad.empty
  | TBaseUnion _       -> Quad.empty
  | TBaseRefine(x,_,p) -> freeVarsForm (Quad.addV x env) p
  | THasTyp(u)         -> freeVarsTT env u
  | TNonNull(t)        -> freeVarsTyp env t
  | TMaybeNull(t)      -> freeVarsTyp env t
  | TTuple(l) ->
      let (xs,ts) = List.split l in
      let env = List.fold_left (fun env x -> Quad.addV x env) env xs in
      Quad.combineList (List.map (freeVarsTyp env) ts)
  | TExists _ -> failwith "freeVars TExists"

and freeVarsForm env = function
  | PEq(w1,w2)       -> Quad.combine (freeVarsWal env w1) (freeVarsWal env w2)
  | PApp(_,ws)       -> Quad.combineList (List.map (freeVarsWal env) ws)
  | PTru | PFls      -> Quad.empty
  | PUn(HasTyp(w,u)) -> Quad.combine (freeVarsWal env w) (freeVarsTT env u)
  | PPacked(w)       -> freeVarsWal env w
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
  | UArr((ts,ls,hs),x,t1,h1,t2,h2) ->
      let env = List.fold_left (fun env t -> Quad.addT t env) env ts in
      let env = List.fold_left (fun env l -> Quad.addL l env) env ls in
      let env = List.fold_left (fun env h -> Quad.addH h env) env hs in
      let xs = VVars.elements (heapBinders (snd h1)) in
      let env' = List.fold_left (fun env x -> Quad.addV x env) env (x::xs) in
      Quad.combine (freeVarsWorld env (t1,h1)) (freeVarsWorld env' (t2,h2))

and freeVarsHeap env (hs,cs) =
  let free =
    List.fold_left
    (fun acc h -> if Quad.memH h env then acc else Quad.addH h acc)
    Quad.empty hs in
  let xs = VVars.elements (heapBinders cs) in
  let env = List.fold_left (fun env x -> Quad.addV x env) env xs in
  List.fold_left (fun acc -> function
    | (l,HConc(_,t))
    | (l,HConcObj(_,t,_)) ->
         Quad.combineList [freeVarsLoc env l; freeVarsTyp env t; acc]
  ) free cs

and freeVarsWorld env (t,h) =
  let xs = VVars.elements (heapBinders (snd h)) in
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

end


(******
   the masterSubstX routines do all four kinds of substitution

     1. value var   -[w/x]
     2. type var    Inst(-,A,T)
     3. loc var     -[l/L]
     4. heap var    -[E/H]

   with capture-avoidance for the two kinds of binding forms

     1. types       {x|p} (and sugar forms {x:B|p} and (x:T,y:S))
     2. arrows      [A_i;L_i;H_i] x:T1/E1 -> T2/E2
*)

(*
(* note: this one returns a walue, not a value *)
let rec masterSubstVal subst = function
  | VVar(x) -> (* value variable substitution *)
      let (sub,_,_,_) = subst in
      if List.mem_assoc x sub then List.assoc x sub else WVal (VVar x)
  | VBase(x) -> WVal (VBase x)
  | VEmpty   -> WVal VEmpty
  | VExtend(v1,v2,v3) -> begin
      match List.map (masterSubstWal subst) [WVal v1; WVal v2; WVal v3] with
        | [WVal(v1');WVal(v2');WVal(v3')] -> WVal (VExtend (v1', v2', v3'))
        | _ -> failwith "masterSubstVal VExtend"
    end
  (* TODO might need to recurse into lambdas, if they appear in formulas *)
  | VFun _ as v -> WVal v
*)

let rec masterSubstWal subst = function

  | WVal(VVar(x)) -> (* value variable substitution *)
      let (sub,_,_,_) = subst in
      if List.mem_assoc x sub then List.assoc x sub else WVal (VVar x)
  | WVal(VBase(x))       -> WVal (VBase x)
  | WVal(VEmpty)         -> WVal VEmpty
  | WVal(VExtend _ as v) -> WVal v
  | WVal(VFun _ as v)    -> WVal v
  (* TODO might need to recurse into lambdas, if they appear in formulas *)

  | WBot            -> WBot
  | WApp(s,ws)      -> WApp (s, List.map (masterSubstWal subst) ws)
  | WHeapSel(h,l,w) -> WHeapSel (masterSubstHeap subst h,
                               masterSubstLoc subst l,
                               masterSubstWal subst w)
  | WObjSel(ds,k,h,l) ->
      WObjSel (List.map (masterSubstWal subst) ds, masterSubstWal subst k,
               masterSubstHeap subst h, masterSubstLoc subst l)

and masterSubstForm subst = function
  | PEq(w1,w2)  -> PEq (masterSubstWal subst w1, masterSubstWal subst w2)
  | PApp(s,ws)  -> PApp (s, List.map (masterSubstWal subst) ws)
  | PTru        -> PTru
  | PFls        -> PFls
  | PConn(s,ps) -> PConn (s, List.map (masterSubstForm subst) ps)
  | PPacked(w)  -> PPacked (masterSubstWal subst w)
  | PUn(HasTyp(w,UVar(x))) -> (* type variable instantiation *)
      let w = masterSubstWal subst w in
      let (_,sub,_,_) = subst in
      if List.mem_assoc x sub then applyTyp (List.assoc x sub) w
      else PUn (HasTyp (w, UVar x))
  | PUn(HasTyp(w,u)) ->
      PUn (HasTyp (masterSubstWal subst w, masterSubstTT subst u))
  | PHeapHas(h,l,w) ->
      PHeapHas (masterSubstHeap subst h,
                masterSubstLoc subst l,
                masterSubstWal subst w)
  | PHas(w,ws) ->
      PHas (masterSubstWal subst w, List.map (masterSubstWal subst) ws)
  | PDomEq(w,ws) ->
      PDomEq (masterSubstWal subst w, List.map (masterSubstWal subst) ws)
  | PEqMod(x,y,z) ->
      PEqMod (masterSubstWal subst x,
              masterSubstWal subst y,
              List.map (masterSubstWal subst) z)
  | PObjHas(ds,k,h,l) ->
      PObjHas (List.map (masterSubstWal subst) ds, masterSubstWal subst k,
               masterSubstHeap subst h, masterSubstLoc subst l)
  | PAll _ -> failwith "masterSubstForm: PAll shouldn't appear"

and masterSubstTyp subst = function
  | TTop            -> TTop
  | TBot            -> TBot
  | TBaseUnion(l)   -> TBaseUnion l
  | TNonNull(t)     -> TNonNull (masterSubstTyp subst t)
  | TMaybeNull(t)   -> TMaybeNull (masterSubstTyp subst t)
  | THasTyp(UVar(x)) -> (* type variable instantiation *)
      let (_,sub,_,_) = subst in
      if List.mem_assoc x sub then List.assoc x sub else THasTyp (UVar x)
  | THasTyp(u) -> THasTyp (masterSubstTT subst u)
  (* binding forms *)
  | TRefinement(x,p) ->
      let subst = MasterSubst.removeVVars [x] subst in
      let (x,p) = freshenRawTyp (MasterSubst.freeVars subst) x p in
      TRefinement (x, masterSubstForm subst p)
  | TBaseRefine(x,t,p) ->
      let subst = MasterSubst.removeVVars [x] subst in
      let (x,p) = freshenRawTyp (MasterSubst.freeVars subst) x p in
      TBaseRefine (x, t, masterSubstForm subst p)
  | TTuple(l) ->
      let subst = MasterSubst.removeVVars (List.map fst l) subst in
      let l = freshenDepTuple (MasterSubst.freeVars subst) l in
      TTuple (List.map (fun (x,t) -> (x, masterSubstTyp subst t)) l)
  | TExists _ -> failwith "masterSubst TExists"

and masterSubstTT subst = function
  | UNull   -> UNull
  | UVar(x) -> UVar x (* note: type instantiation happens at w::A, not here *)
  | URef(l) -> URef (masterSubstLoc subst l)
  | UArray(t) -> UArray (masterSubstTyp subst t)
  (* binding form *)
  | UArr((ts,ls,hs),x,t1,h1,t2,h2) ->
      let xs = VVars.elements (heapBinders (snd h1)) in
      let subst =
        subst |> MasterSubst.removeVVars (x::xs)
              |> MasterSubst.removeTVars ts
              |> MasterSubst.removeLVars ls
              |> MasterSubst.removeHVars hs in
      let (substHeapBinders,h1) = freshenHeap (MasterSubst.freeVars subst) h1 in
      let (x',t1)  = freshenDomain (MasterSubst.freeVars subst) x t1 in
      let subst = (* need these because x and xs may appear free in t2/h2 *)
        MasterSubst.extendVSubst ((x, wVar x')::substHeapBinders) subst in
      let t1 = masterSubstTyp subst t1 in
      let t2 = masterSubstTyp subst t2 in
      let h1 = masterSubstHeap subst h1 in
      let h2 = masterSubstHeap subst h2 in
      UArr ((ts,ls,hs), x', t1, h1, t2, h2)

and masterSubstHeap subst (hs,cs) =
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
      | (l,HConc(x,s)) ->
          let subst = MasterSubst.removeVVars [x] subst in
          (masterSubstLoc subst l, HConc (x, masterSubstTyp subst s))
      | (l,HConcObj(x,s,l')) ->
          let subst = MasterSubst.removeVVars [x] subst in
          (masterSubstLoc subst l,
           HConcObj (x, masterSubstTyp subst s, masterSubstLoc subst l'))
    ) cs
  in
  (hs, cs)

and masterSubstLoc subst = function
  | LocConst(x) -> LocConst x
  | LocVar(x) -> (* location variable substitution *)
      let (_,_,sub,_) = subst in
      if List.mem_assoc x sub then List.assoc x sub else LocVar x

(* [[T]](w) *)
and applyTyp t w =
  match t with
    | TRefinement(y,f) -> masterSubstForm ([(y,w)],[],[],[]) f
    | TTop             -> PTru
    | TBot             -> PFls
    | THasTyp(u)       -> PUn (HasTyp (w, u))
    | TNonNull(t)      -> pAnd [applyTyp t w; pNot (PEq (w, wNull))]
    | TMaybeNull(t)    -> pOr [applyTyp t w; PEq (w, wNull)]
    | TBaseUnion([t])  -> PEq (tag w, wStr t)
    | TBaseUnion(l)    -> pOr (List.map (fun t -> PEq (tag w, wStr t)) l)
    | TBaseRefine(y,t,p) ->
        let p = pAnd [PEq (tag (wVar y), wStr t); p] in
        masterSubstForm ([(y,w)],[],[],[]) p
    | TTuple(l) ->
        let (vars,typs) = List.split l in
        let subst = Utils.map_i (fun x i -> (x, sel w (wProj i))) vars in
        let subst = (subst,[],[],[]) in
        let has =
          PHas (w, List.map wProj (Utils.list0N (pred (List.length l)))) in
        let sels =
          Utils.map_i
            (fun t i -> applyTyp (masterSubstTyp subst t) (sel w (wProj i)))
            typs
        in
        pAnd (PEq (tag w, wStr "Dict") :: has :: sels)
    | TExists(x,t,s) ->
        pAnd [applyTyp t (wVar x); applyTyp s w]

(***** the helpers that rename binders to avoid capture *****)

and freshenRawTyp free x p =
  if Quad.memV x free then
    let x' = freshVar x in
    let p' = masterSubstForm ([(x, wVar x')],[],[],[]) p in
    (x', p')
  else
    (x, p)

and freshenDepTuple free l =
  let binderSubst =
    List.fold_left
      (fun acc x -> if Quad.memV x free then (x, freshVar x)::acc else acc)
      [] (List.map fst l) in
  let subst = (List.map (fun (x,x') -> (x, wVar x')) binderSubst, [], [], []) in
  List.map (fun (x,t) ->
    let t = masterSubstTyp subst t in
    if List.mem_assoc x binderSubst
    then (List.assoc x binderSubst, t)
    else (x, t)
  ) l

and freshenHeap free (hs,cs) =
  let binderSubst =
    List.fold_left (fun acc -> function
      | (_,HConc(x,_))
      | (_,HConcObj(x,_,_)) ->
          if Quad.memV x free then (x, freshVar x)::acc else acc
    ) [] cs
  in
  let binderSubstW = List.map (fun (x,x') -> (x, wVar x')) binderSubst in
  let subst = (binderSubstW,[],[],[]) in
  let cs =
    List.map (function
      | (l,HConc(x,s)) ->
          let x =
            if List.mem_assoc x binderSubst
            then List.assoc x binderSubst
            else x in
          (l, HConc (x, masterSubstTyp subst s))
      | (l,HConcObj(x,s,l')) ->
          let x =
            if List.mem_assoc x binderSubst
            then List.assoc x binderSubst
            else x in
          (l, HConcObj (x, masterSubstTyp subst s, l'))
    ) cs
  in
  (binderSubstW, (hs, cs))

and freshenDomain free x t =
  match freshenDepTuple free [(x,t)] with
    | [(x',t')] -> (x', t')
    | _         -> failwith "freshenDomain: impossible"


(***** Expression Substitution ************************************************)

(* needed only by the parser, when desugaring letrecs *)

let substVarInExp z x e =
  if x = z then e
  else failwith "substVarInExp: letrec using a freshvar for mono def?"


(***** Expanding pre-formulas *************************************************)

let oc_unroll = open_out (Settings.out_dir ^ "unroll.txt")

let printUnroll cap p q =
  fpr oc_unroll "%s\n%s %s\n\n%s\n\n" (String.make 80 '-') cap
    (prettyStrForm p) (prettyStrForm q)

let printUnrollWal cap w1 w2 =
  fpr oc_unroll "%s\n%s %s\n\n%s\n\n" (String.make 80 '-') cap
    (prettyStrWal w1) (prettyStrWal w2)

let sHole i = spr "__hole__%d" i
let wHole i = wVar (sHole i)

(***** expand PHeapHas *****)

let rec expandHH (hs,cs) l k =
  let p =
    if not (List.mem_assoc l cs) then PHeapHas ((hs,[]), l, k)
    else begin
      match List.assoc l cs with
        | HConcObj(d,_,l') -> 
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
        | HConcObj(d,_,l') -> foo (ds @ [wVar d]) l'
        | _ -> failwith "expandOH: not conc constraint"
    end
  in
  let p = foo ds l in
  printUnroll "expand" (PObjHas(ds,k,(hs,cs),l)) p;
  p

(***** expand WHeapSel *****)

(* TODO *)
let expandHS p (hs,cs) l k =
  failwith "expandHS"

(***** expand WObjSel *****)

let expandOS ds k (hs,cs) l =
  let rec foo ds l =
    if not (List.mem_assoc l cs) then WObjSel (ds, k, (hs,[]), l)
    else begin
      match List.assoc l cs with
        | HConcObj(d,_,l') -> foo (ds @ [wVar d]) l'
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
(* TODO TODO
  | WHeapSel(e,l,k)   -> expandHS e l k
*)
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
    failwith (spr "embedObjHas: constraints should've been expanded:\n\n%s"
      (prettyStrForm (PObjHas(ds,k,(hs,cs),l))));
  let ps = List.map (fun d -> embedHas d [k]) ds in
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
      (prettyStrWal (WObjSel(ds,k,(hs,cs),l))));
  let rec foo = function
    | [] ->
        let subst = ([sHole i, WHeapSel ((hs,[]), l, k)], [], [], []) in
        masterSubstForm subst ctx
    | d::ds ->
        let subst = ([sHole i, sel d k], [], [], []) in
        pAnd [pImp (embedHas d [k]) (masterSubstForm subst ctx);
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

let embedForm p = p |> embedForm1 |> embedObjSelsInsideOut


