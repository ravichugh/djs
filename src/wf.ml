
open Lang
open LangUtils


(***** Helpers ****************************************************************)

let depTupleBinders t =
  let rec foo acc = function
    | TTuple(l) -> 
        let (xs,ts) = List.split l in
        let acc = List.fold_left (fun acc x -> Var(x,tyAny)::acc) acc xs in
        List.fold_left foo acc ts
    | TNonNull(t) | TMaybeNull(t) -> foo acc t
    | _ -> acc
  in foo [] t

(*
let varBoundInG x g =
  List.exists (function Var(y,_) when x = y -> true | _ -> false) g
*)

(* TODO 11/22 *)

let rec isTopLevelExistential x = function
  | TExists(y,_,t) -> x = y || isTopLevelExistential x t
  | _              -> false

let varBoundInG x g =
  List.exists (function
    | Var(y,t) -> x = y || isTopLevelExistential x t
    | _        -> false
  ) g

(*
let varBoundInH x h =
  List.exists
    (function HConc(y,_) | HConcObj(y,_,_) -> x = y) (* | _ -> false) *)
    (List.map snd (snd h))
*)

(* TODO 11/27: when checking heap wf, don't want to snapshot it first.
   the nice thing about how it was set up is that the entire heap is a
   parameter when checking wf of its constraints (the helper relation).
   so, when looking up a variable binder in H, also need to walk dep
   tuple binders *)

let varBoundInH x h =
  List.exists
    (function HConc(y,t) | HConcObj(y,t,_) ->
       x = y || varBoundInG x (depTupleBinders t))
    (List.map snd (snd h))
  
let varBound x g h = varBoundInG x g || varBoundInH x h

let noDupeFormal errList s l =
  match Utils.someDupe l with
    | None    -> ()
    | Some(x) -> err (errList @ [spr "duplicate %s variable: [%s]" s x])

let heapBinders (_,cs) =
  List.fold_left (fun acc -> function
    | (_,HConc(x,t))
    | (_,HConcObj(x,t,_)) ->
        Var(x,tyAny) :: depTupleBinders t @ acc
  ) [] cs

let envToStrings g =
  let (_,l) =
    List.fold_left (fun (b,acc) -> function
      | Var(x,t) ->
          if x = "end_of_pervasives" then (false, acc)
          else if b = true then (true, (spr "  %s : %s" x (prettyStrTyp t)) :: acc)
          else (false, acc)
      | _ -> (b,acc)
    ) (true,[]) g
  in
  "\nEnvironment:\n" :: l


(***** Well-formedness checks *************************************************)

let rec checkType errList g h t =
  let errList = errList @ [spr "Wf.checkType: %s" (prettyStrTyp t)] in
  match t with
    | TTop | TBot | TBaseUnion _ -> ()
    | THasTyp(u) -> checkTypeTerm errList g h u
    | TNonNull(t) | TMaybeNull(t) -> checkType errList g h t
    | TRefinement(x,p) | TBaseRefine(x,_,p) ->
        checkFormula errList (Var(x,tyAny)::g) h p
    | TTuple(l) ->
        let (vars,typs) = List.split l in
        let g = List.fold_left (fun acc x -> Var(x,tyAny)::acc) g vars in
        List.iter (checkType errList g h) typs
    | TExists(x,t,s) ->
        checkType errList (Var(x,t)::g) h s

and checkFormula errList g h p =
  match p with
    | PTru | PFls         -> ()
    | PEq(w1,w2)          -> List.iter (checkWalue errList g h) [w1;w2]
    | PApp(_,ws)          -> List.iter (checkWalue errList g h) ws
    | PConn(_,ps)         -> List.iter (checkFormula errList g h) ps
    | PHas(w,ws)
    | PDomEq(w,ws)        -> List.iter (checkWalue errList g h) (w::ws)
    | PEqMod(w1,w2,ws)    -> List.iter (checkWalue errList g h) (w1::w2::ws)
    | PPacked(w)          -> checkWalue errList g h w
    | PUn(HasTyp(w,u))    -> (checkWalue errList g h w;
                              checkTypeTerm errList g h u)
    | PHeapHas(h',l,w)    -> (checkHeap errList g h'; (* h not used *)
                              checkLoc errList g h l;
                              checkWalue errList g h w)
    | PObjHas(ds,k,h',l)  -> (List.iter (checkWalue errList g h) (k::ds);
                              checkHeap errList g h';
                              checkLoc errList g h l)
    | PAll _              -> failwith "wfForm: PAll shouldn't appear"

and checkWalue errList g h w =
  match w with
    | WBot               -> ()
    | WVal(v)            -> checkValue errList g h v
    | WApp(_,ws)         -> List.iter (checkWalue errList g h) ws
    | WHeapSel(h',l,w)   -> (checkHeap errList g h'; (* h not used *)
                             checkLoc errList g h l;
                             checkWalue errList g h w)
    | WObjSel(ds,k,h',l) -> (List.iter (checkWalue errList g h) (k::ds);
                             checkHeap errList g h';
                             checkLoc errList g h l)

and checkValue errList g h v =
  match v with
    | VVar(x) ->
        if varBound x g h then ()
        else err (errList @ [spr "unbound variable: [%s]" x] @ envToStrings g)
    | VBase _ | VEmpty -> ()
    | VExtend(v1,v2,v3) -> List.iter (checkValue errList g h) [v1;v2;v3]
    | VFun _ -> () (* not recursing, since lambdas don't appear in formulas *)

and checkTypeTerm errList g h u =
  let errList = errList @ [spr "Wf.checkTypeTerm: %s" (prettyStrTT u)] in
  match u with
    | UNull   -> ()
    | URef(l) -> checkLoc errList g h l
    | UArray(t) -> checkType errList g h t
    | UVar(x) ->
        if List.exists (function TVar(y) -> x = y | _ -> false) g then ()
        else err (errList @ [spr "unbound type variable: [%s]" x])
    | UArr((ts,ls,hs),x,t1,e1,t2,e2) -> begin
        noDupeFormal errList "type" ts;
        noDupeFormal errList "loc" ls;
        noDupeFormal errList "heap" hs;
        let g = List.fold_left (fun acc x -> TVar(x)::acc) g ts in
        let g = List.fold_left (fun acc x -> LVar(x)::acc) g ls in
        let g = List.fold_left (fun acc x -> HVar(x)::acc) g hs in
        let g = g @ [Var(x,tyAny)] @ depTupleBinders t1 in
        (* TODO this shouldn't be checkWorld *)
        checkWorld errList g (t1,e1);
(*
        let g = g @ heapBinders e1 @ [Var(x,tyAny)] @ depTupleBinders t1 in
*)
        let g = g @ heapBinders e1 in
        checkWorld errList g (t2,e2)
      end

and checkHeap errList g h =
  let errList = errList @ [spr "Wf.checkHeap:\n%s" (prettyStrHeap h)] in
  List.iter
    (function x ->
       if List.exists (function HVar(y) -> x = y | _ -> false) g then ()
       else err (errList @ [spr "unbound heap variable: [%s]" x]))
    (fst h);
  checkConstraints errList g h (snd h)

and checkConstraints errList g h = function
  | [] -> ()
  | (l,HConc(x,s))::rest -> begin
      checkLoc errList g h l;
      (if List.exists (function (l',_) -> l = l') rest
       then err (errList @ [spr "loc [%s] bound multiple times" (strLoc l)])
       else ());
      checkType errList g h s;
      checkConstraints errList g h rest
    end
  | (l,HConcObj(x,s,l'))::rest -> begin
      checkLoc errList g h l';
      checkConstraints errList g h ((l,HConc(x,s))::rest)
    end

(*
and checkWorld errList g (t,h) =
  checkHeap errList g h;
  checkType errList g h t
*)
and checkWorld errList g = function
  | (TExists(x,t,s),h) -> checkWorld errList (Var(x,t)::g) (s,h)
  | (t,h) -> (checkHeap errList g h; checkType errList g h t)

and checkLoc errList g h = function
  | LocConst _ -> ()
  | LocVar(x) ->
      if List.exists (function LVar(y) -> x = y | _ -> false) g then ()
      else err (errList @ [spr "unbound location variable: [%s]" x])

and checkFrame errList g (hs,e,w) =
  let g = List.fold_left (fun acc x -> HVar(x)::acc) g hs in
  checkHeap errList g e;
  let g = g @ heapBinders e in
  checkWorld errList g w


(***** Entry point ************************************************************)

let typ cap      = checkType      [spr "Wf.typ: %s" cap]
let heap cap     = checkHeap      [spr "Wf.heap: %s" cap]
let world cap    = checkWorld     [spr "Wf.world: %s" cap]
let typeTerm cap = checkTypeTerm  [spr "Wf.typeTerm: %s" cap]
let frame cap    = checkFrame     [spr "Wf.frame: %s" cap]

