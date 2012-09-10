
open Lang
open LangUtils


(***** Helpers ****************************************************************)

let depTupleBindersEnv t =
  List.map (fun x -> Var (x, tyAny)) (depTupleBinders t)

let varBound x g =
  List.exists (function Var(y,t) -> x = y | _ -> false) g

let noDupeFormal errList s l =
  match Utils.someDupe l with
    | None    -> ()
    | Some(x) -> err (errList @ [spr "duplicate %s variable: [%s]" s x])

let heapBinders (_,cs) =
  List.fold_left (fun acc -> function
    | (_,HStrong(None,t,_)) -> depTupleBindersEnv t @ acc
    | (_,HStrong(Some(x),t,_)) -> Var(x,tyAny) :: depTupleBindersEnv t @ acc
    | (_,HWeak _) -> acc
  ) [] cs

let envToStrings g =
  let (_,l) =
    List.fold_left (fun (b,acc) -> function
      | Var(x,t) ->
          if x = "end_of_pervasives" then (false, acc)
          else if b = true then (true, (spr "  %s : %s" x (strTyp t)) :: acc)
          else (false, acc)
      | _ -> (b,acc)
    ) (true,[]) g
  in
  "\nEnvironment:\n" :: l


(***** Well-formedness checks *************************************************)

let rec checkType errList g t =
  let errList = errList @ [spr "Wf.checkType: %s" (strTyp t)] in
  match t with
    | TBaseUnion _ -> ()
    | TNonNullRef(l) -> checkLoc errList g l
    | TMaybeNullRef(l,p) -> (checkLoc errList g l; checkFormula errList g p)
    | TRefinement(x,p) -> checkFormula errList (Var(x,tyAny)::g) p
    | TQuick(x,qt,p) ->
        let _ = checkQuickTyp errList (Var(x,tyAny)::g) qt in
        checkFormula errList (Var(x,tyAny)::g) p
(*
    | TTuple(l) ->
        let (vars,typs) = List.split l in
        let g = List.fold_left (fun acc x -> Var(x,tyAny)::acc) g vars in
        List.iter (checkType errList g) typs
*)

and checkPrenexTyp errList g t =
  let errList = errList @ [spr "Wf.checkPrenexTyp: %s" (strPrenexTyp t)] in
  match t with
    | Typ(s) -> checkType errList g s
    | TExists(x,t,s) -> checkPrenexTyp errList (Var(x,t)::g) s

and checkQuickTyp errList g = function
  | QBase _ -> ()
  | QBoxes(l) -> List.iter (checkTypeTerm errList g) l
  | QRecd(l,_) -> List.iter (checkType errList g) (List.map snd l)
  | QTuple(l,_) ->
      let binders = bindersOfDepTuple l in
      let g = List.fold_left (fun acc x -> Var(x,tyAny)::acc) g binders in
      List.iter (checkType errList g) (List.map snd l)

and checkFormula errList g p =
  match p with
    | PEq(w1,w2)          -> List.iter (checkWalue errList g) [w1;w2]
    | PApp(_,ws)          -> List.iter (checkWalue errList g) ws
    | PConn(_,ps)         -> List.iter (checkFormula errList g) ps
    | PHas(w,ws)
    | PDomEq(w,ws)        -> List.iter (checkWalue errList g) (w::ws)
    | PEqMod(w1,w2,ws)    -> List.iter (checkWalue errList g) (w1::w2::ws)
    | PHasTyp(w,u)        -> (checkWalue errList g w;
                              checkTypeTerm errList g u)
    | PHeapHas(h',l,w)    -> (checkHeap errList g h'; (* h not used *)
                              checkLoc errList g l;
                              checkWalue errList g w)
    | PObjHas(ds,k,h',l)  -> (List.iter (checkWalue errList g) (k::ds);
                              checkHeap errList g h';
                              checkLoc errList g l)
    | PAll _              -> failwith "wfForm: PAll shouldn't appear"

and checkWalue errList g w =
  match w with
    | WBot               -> ()
    | WVal(v)            -> checkValue errList g v
    | WApp(_,ws)         -> List.iter (checkWalue errList g) ws
    | WHeapSel(h',l,w)   -> (checkHeap errList g h'; (* h not used *)
                             checkLoc errList g l;
                             checkWalue errList g w)
    | WObjSel(ds,k,h',l) -> (List.iter (checkWalue errList g) (k::ds);
                             checkHeap errList g h';
                             checkLoc errList g l)

and checkValue errList g v =
  match v.value with
    | VVar(x) ->
        if varBound x g then ()
        (* else err (errList @ [spr "unbound variable: [%s]" x] @ envToStrings g) *)
        else err (errList @ [spr "unbound variable: [%s]" x])
    | VBase _ | VNull | VEmpty -> ()
    (* | VNewObjRef _ -> () *)
    | VExtend(v1,v2,v3) -> List.iter (checkValue errList g) [v1;v2;v3]
    | VArray(_,vs) | VTuple(vs) -> List.iter (checkValue errList g) vs
    | VFun _ -> () (* not recursing, since lambdas don't appear in formulas *)

and checkTypeTerm errList g u =
  let errList = errList @ [spr "Wf.checkTypeTerm: %s" (strTT u)] in
  match u with
    | UNull -> ()
    | URef(l) -> checkLoc errList g l
    | UArray(t) -> checkType errList g t
    | UVar(x) ->
        if List.exists (function TVar(y) -> x = y | _ -> false) g then ()
        else err (errList @ [spr "unbound type variable: [%s]" x])
    | UArrow((ts,ls,hs),x,t1,e1,t2,e2) -> begin
        noDupeFormal errList "type" ts;
        noDupeFormal errList "loc" ls;
        noDupeFormal errList "heap" hs;
        let g = List.fold_left (fun acc x -> TVar(x)::acc) g ts in
        let g = List.fold_left (fun acc x -> LVar(x)::acc) g ls in
        let g = List.fold_left (fun acc x -> HVar(x)::acc) g hs in
        let g = g @ [Var(x,tyAny)] @ depTupleBindersEnv t1 in
        (* TODO this shouldn't be checkWorld *)
        checkWorld errList g (t1,e1);
(*
        let g = g @ heapBinders e1 @ [Var(x,tyAny)] @ depTupleBinders t1 in
*)
        let g = g @ heapBinders e1 in
        checkWorld errList g (t2,e2)
      end
    | UMacro _ -> () (* could check macro table in TcDref3 *)

and checkHeap errList g h =
  let errList = errList @ [spr "Wf.checkHeap:\n%s" (strHeap h)] in
  List.iter
    (function x ->
       if List.exists (function HVar(y) -> x = y | _ -> false) g then ()
       else err (errList @ [spr "unbound heap variable: [%s]" x]))
    (fst h);
  let g = g @ heapBinders h in
  checkConstraints errList g (snd h)

and checkConstraints errList g = function
  | [] -> ()
  | (l,HStrong(x,s,lo))::rest -> begin
      checkLoc errList g l;
      (if List.exists (function (l',_) -> l = l') rest
       then err (errList @ [spr "loc [%s] bound multiple times" (strLoc l);
         "perhaps you are running into the cap-avoiding subst bug..."])
       else ());
      checkType errList g s;
      (match lo with Some(l') -> checkLoc errList g l' | None -> ());
      checkConstraints errList g rest
    end
  | (l,HWeak(tok))::rest -> begin
      checkLoc errList g l;
      (match tok with Frzn -> () | Thwd(l') -> checkLoc errList g l');
      checkConstraints errList g rest;
    end

and checkWorld errList g (t,h) =
  checkHeap errList g h;
  checkType errList g t

and checkLoc errList g = function
  (* TODO 8/13 want to check weaklocs also, but they go out of scope since
     EWeak is a binding form *)
(*
  | LocConst _ as l ->
      if isStrongLoc l then ()
      else if List.exists (function WeakLoc(l',_,_) -> l = l' | _ -> false) g then ()
      else err (errList @ [spr "unbound weak location: [%s]" (strLoc l)])
*)
  | LocConst _ -> ()
  | LocVar(x) ->
      if List.exists (function LVar(y) -> x = y | _ -> false) g then ()
      else err (errList @ [spr "unbound location variable: [%s]" x])

and checkFrame errList g (hs,e,w) =
  let g = List.fold_left (fun acc x -> HVar(x)::acc) g hs in
  checkHeap errList g e;
  let g = g @ heapBinders e in
  checkWorld errList g w

let checkType = BNstats.time "Wf.checkType" checkType
let checkFormula = BNstats.time "Wf.checkFormula" checkFormula
let checkHeap = BNstats.time "Wf.checkHeap" checkHeap
let checkConstraints = BNstats.time "Wf.checkConstraints" checkConstraints
let checkWorld = BNstats.time "Wf.checkWorld" checkWorld
let checkTypeTerm = BNstats.time "Wf.checkTypeTerm" checkTypeTerm
let checkFrame = BNstats.time "Wf.checkFrame" checkFrame


(***** Entry point ************************************************************)

let typ cap      = checkType      [spr "Wf.typ: %s" cap]
let prenexTyp cap= checkPrenexTyp [spr "Wf.prenexTyp: %s" cap]
let heap cap     = checkHeap      [spr "Wf.heap: %s" cap]
let world cap    = checkWorld     [spr "Wf.world: %s" cap]
let typeTerm cap = checkTypeTerm  [spr "Wf.typeTerm: %s" cap]
let frame cap    = checkFrame     [spr "Wf.frame: %s" cap]

let typ = BNstats.time "Wf.typ" typ
let prenexTyp = BNstats.time "Wf.prenexTyp" prenexTyp

