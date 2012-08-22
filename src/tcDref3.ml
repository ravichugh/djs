
open Lang
open LangUtils
(* open TcUtils *)


let oc_elim = open_out (Settings.out_dir ^ "elim.txt")

(**** Selfify *****************************************************************)

(* Rather than blindly returning {v=x}, check if the type of x is a syntactic
   type, and if so, keep that exposed at the top level so that don't need
   as many extractions. *)

let addPredicate p = function
  | PTru -> p
  | PConn("and",ps) -> pAnd (ps @ [p])
  | q -> pAnd [q;p]

let selfifyVar g x =
  try
    let eqX = eq theV (wVar x) in
    begin match List.find (function Var(y,_) -> x = y | _ -> false) g with
      | Var(_,TSelfify(t,p)) -> TSelfify (t, addPredicate eqX p)
      | Var(_,TMaybeNull(t)) -> TSelfify (TMaybeNull(t), eqX)
      | Var(_,THasTyp(us,p)) -> THasTyp (us, addPredicate eqX p)
      | _                    -> ty eqX
    end
  with Not_found ->
    err [spr "selfifyVar: var not found: [%s]" x]
  
let selfifyVal g = function
  | {value=VVar(x)} -> selfifyVar g x
  | v               -> ty (PEq (theV, WVal v))


(**** Environment operations **************************************************)

let removeLabels g =
  List.filter (function Lbl _ -> false | _ -> true) g

let printBinding (x,s) =
  if !Settings.printAllTypes || !depth = 0 then begin
    setPretty true;
    Log.log2 "\n%s :: %s\n" x (strTyp s);
    setPretty false;
    flush stdout;
    ()
  end

(* TODO check this *)
let addDepTupleBindings g t =
  let rec foo (accN,accG) = function
    | TTuple(l) ->
        List.fold_left (fun (accN,accG) (x,s) ->
          Zzz.addBinding ~isNew:true x PTru;
          (succ accN, Var(x,s) :: accG)
        ) (accN,accG) l
    | TNonNull(t) | TMaybeNull(t) -> foo (accN, accG) t
    | _ -> (accN, accG)
  in
  let rec bar = function
    | TTuple(l) ->
        List.iter (fun (x,s) ->
          Zzz.addBinding ~isNew:false x (applyTyp s (wVar x));
          printBinding (x,s);
        ) l
    | TNonNull(t) | TMaybeNull(t) -> bar t
    | _ -> ()
  in
(*
  let rec baz g = function
    | TTuple(l) -> List.iter (tryUnfold g) l
    | TNonNull(t) | TMaybeNull(t) -> baz g t
    | _ -> ()
  in
*)
  let (n,g) = foo (0,g) t in (* first, get all vars in scope *)
  bar t;                     (* second, assert all their types *)
(*
  baz g t;                   (* finally, try to do non-det unfold *)
*)
  (n, g)

let printHeapEnv (hs,cs) =
  if (!Settings.printAllTypes || !depth = 0) then begin
    Log.log1 "\n/ %s ++\n" (String.concat "++" hs);
    List.iter (function
      | (m,HEWeakTok(x)) -> Log.log2 "  %s |-> %s\n" (strLoc m) (strThawState x)
      | (l,HEConc(v)) -> Log.log2 "  %s |-> %s\n" (strLoc l) (prettyStrVal v)
      | (l,HEConcObj(v,l')) -> Log.log3 "  %s |-> %s |> %s\n"
                                 (strLoc l) (prettyStrVal v) (strLoc l')) cs;
  end

(* no longer prints heap, so must typing rules should manually print heap *)
let rec tcAddBinding ?(isNew=true) g x = function
  | TExists(y,t1,t2) ->
      let (n,g) = tcAddBinding ~isNew:true g y t1 in
      let (m,g) = tcAddBinding ~isNew g x t2 in
      (n + m, g)
  | s ->
      let (n,g) = addDepTupleBindings g s in (* TODO 8/16 check this *)
      let g = Var(x,s) :: g in
      let _ = Zzz.addBinding ~isNew x (applyTyp s (wVar x)) in
      let _ = printBinding (x,s) in
      (n + 1, g)

(* the list l of bindings may mutually refer to each other so
   make a first pass to get all binders in scope in the logic and then
   make a second pass to push their real types and convert to heap env *)
(* TODO only do first pass if the bindings are not well-scoped left to right *)
let tcAddManyBindings l g =
  let (n,g) =
    List.fold_left (fun (n,g) (x,t) ->
      let (k,g) = tcAddBinding ~isNew:true g x tyAny in (n + k, g)
    ) (0,g) l in
  let g =
    List.fold_left (fun g (x,t) ->
      snd (tcAddBinding ~isNew:false g x t)
    ) g l in
  (n, g)

let tcRemoveBindingN n =
  for i = 1 to n do Zzz.removeBinding () done

let findWeakLoc g m =
  try
    begin match List.find (function WeakLoc(y,_,_) -> m = y | _ -> false) g with
      | WeakLoc(_,t,l) -> (t, l)
      | _              -> failwith "findWeakLoc: impossible"
    end
  with Not_found ->
    err [spr "findWeakLoc: not found: [%s]" (strLoc m)]


(***** Heap operations ********************************************************)

(* looks for the first matching constraint *)
let findCell l (_,cs) =
  try Some (snd (List.find (fun (l',_) -> l = l') cs))
  with Not_found -> None

let findAndRemoveCell l (hs,cs) =
  match findCell l (hs,cs) with
    | Some(cell) -> Some (cell, (hs, List.remove_assoc l cs))
    | None       -> None

let applyFrame (hAct: heapenv) (hvars,h1,(t2,h2)) : world =
  match hvars with
    | [x] when h1 = ([x],[]) && h1 = h2 ->
        let (hs,cs) = hAct in
        let cs =
          List.map (function
            | (l,HEWeakTok(x)) -> (l, HWeakTok x)
            | (l,HEConc(v)) -> (l, HConc (None, valToSingleton v))
            | (l,HEConcObj(v,l')) -> (l, HConcObj (None, valToSingleton v, l'))
          ) cs in
        (t2, (hs, cs))
    | _ ->
        failwith "applyFrame: need to implement general case"

(* TODO 8/14 need to deal with depTupleBinders as in snapshot below? *)
let heapEnvOfHeap (hs,cs) =
  let (bindings,cs) =
    List.fold_left (fun (acc1,acc2) -> function
      | (m,HWeakTok(x)) -> (acc1, (m, HEWeakTok x) :: acc2)
      | (l,HConc(None,t)) -> (acc1, (l, HEConc (valOfSingleton t)) :: acc2)
      | (l,HConcObj(None,t,l')) ->
          (acc1, (l, HEConcObj (valOfSingleton t, l')) :: acc2)
      | (l,HConc(Some(x),t)) ->
          ((x,t) :: acc1, (l, HEConc (vVar x)) :: acc2) 
      | (l,HConcObj(Some(x),t,l')) ->
          ((x,t) :: acc1, (l, HEConcObj (vVar x, l')) :: acc2) 
    ) ([],[]) cs
  in (bindings, (hs, cs))

let freshenWorld (t,(hs,cs)) =
  let vSubst =
    List.rev (List.fold_left (fun acc -> function
      | (_,HConc(Some(x),_))
      | (_,HConcObj(Some(x),_,_)) -> (x, freshVar x) :: acc
      | (_,HConc(None,_)) | (_,HConcObj(None,_,_)) -> acc
      | (_,HWeakTok _) -> acc
    ) [] cs) in
  let subst = (List.map (fun (x,y) -> (x, wVar y)) vSubst, [], [], []) in
  let cs =
    List.fold_left (fun acc -> function
      | (l,HConc(Some(x),s)) ->
          let x' = List.assoc x vSubst in
          let s' = substTyp subst s in (l,HConc(Some(x'),s')) :: acc
      | (l,HConcObj(Some(x),s,l')) ->
          let x' = List.assoc x vSubst in
          let s' = substTyp subst s in (l,HConcObj(Some(x'),s',l')) :: acc
      | (l,HConc(None,s)) -> (l, HConc (None, s)) :: acc
      | (l,HConcObj(None,s,l')) -> (l, HConcObj (None, s, l')) :: acc
      | (l,HWeakTok(tok)) -> (l, HWeakTok tok) :: acc
    ) [] cs in
  let t = substTyp subst t in
  (t, (hs, cs))

let substHeapEnvVal subst v =
  match substWal subst (WVal v) with
    | WVal(v') -> v'
    | _ -> failwith "substHeapEnvVal: impossible"

let substHeapEnv subst (hs,cs) =
  let cs =
    List.map (function
      | (l,HEConc(v)) ->
          (substLoc subst l, HEConc (substHeapEnvVal subst v))
      | (l,HEConcObj(v,l')) ->
          (substLoc subst l, HEConcObj (substHeapEnvVal subst v,
                                        substLoc subst l'))
      | (l,HEWeakTok(Frzn)) ->
          (substLoc subst l, HEWeakTok Frzn)
      | (l,HEWeakTok(Thwd(l'))) ->
          (substLoc subst l, HEWeakTok (Thwd (substLoc subst l')))
    ) cs
  in
  (hs, cs)


(***** Manipulating existential types *****************************************)

let checkWfHeap = ref true

let rec mkExists s = function
  | (x,t)::l -> TExists (x, t, mkExists s l)
  | []       -> s

(* Add existentials and check well-formedness. Algorithmic typing should
   always synthesize well-formed types, but doing this as a sanity check. *)
let finishLet cap g y l ((s,h): (typ*heapenv)) : typ * heapenv =
  if y = "end_of_pervasives" then checkWfHeap := false;
  if y = "end_of_djs_prelude" then checkWfHeap := false;
  let w = (mkExists s l, h) in
  (* TODO 8/14 should also check that the heapenv is well formed *)
  if !checkWfHeap then Wf.typ (spr "finishLet: %s" cap) g (fst w);
  w

let avoidSingletonExistentials (l,h) =
  List.fold_left (fun (l,h) (x,t) ->
    match maybeValOfSingleton t with
      | Some(v) -> (l, substHeapEnv ([x,WVal(v)],[],[],[]) h)
      | None    -> ((x,t)::l, h)
  ) ([],h) l

let rec elimSingletonExistentials (t,h) =
  match t with
    | TExists(x,t1,t2) ->
        (match maybeValOfSingleton t1 with
           | Some(v) ->
               let _ = fpr oc_elim "avoided singleton %s\n%s\n\n" x
                         (prettyStrTyp t1) in
               let subst = ([x,WVal(v)],[],[],[]) in
               elimSingletonExistentials
                 (substTyp subst t2, substHeapEnv subst h)
           | None ->
               let _ = fpr oc_elim "did not avoid singleton %s\n" x in
               let (t2,h) = elimSingletonExistentials (t2,h) in
               (TExists (x,t1,t2), h))
    | _ -> (t, h)

let stripExists t =
  let rec foo acc = function
    | TExists(x,t,s) -> foo ((x,t)::acc) s
    | s              -> (acc, s)
  in
  let (l,s) = foo [] t in
  (List.rev l, s)


(***** Misc operations ********************************************************)

(* TODO when adding abstract refs, revisit these two *)
(* 4/10 adding strong param to refsTermsOf, to use different filtering funcs *)

(* TODO might want a separate version for local inf, where maybenulls should be
   considered, and a version for type checking, where they shouldn't *)
let refTermsOf g ?(strong=None) = function
  (* 3/14 the MaybeNull case is so that thawed references can be passed
     to the object primitives *)
  | TMaybeNull(THasTyp([URef(l)],_))
  | TSelfify(TMaybeNull(THasTyp([URef(l)],_)),_) (* TODO 3/14 *)
  | THasTyp([URef(l)],_) ->
      let _ = Log.log1 "don't call extract [Ref(%s)]\n" (strLoc l) in
      [URef l]
  | t ->
      let _ = Log.log1 "call extract refTermsOf [%s]\n" (prettyStrTyp t) in
      let filter = function
        | URef(l) -> (match strong with
                        | None -> true
                        | Some(b) -> if b then not (isWeakLoc l) else isWeakLoc l)
        | _       -> false in
      TypeTerms.elements (Sub.mustFlow g t ~filter)
(*
      let isConcRef = function URef _ -> true | _ -> false in
      TypeTerms.elements (Sub.mustFlow g t ~filter:isConcRef)
*)

let singleRefTermOf ?(strong=None) cap g t =
  match refTermsOf g ~strong t, strong with
    | [URef(l)], None -> l
    | [URef(l)], Some(true) ->
        if isStrongLoc l then l
        else err [cap; spr "[%s] flows to value, but is not strong" (strLoc l)]
    | [URef(l)], Some(false) ->
        if isWeakLoc l then l
        else err [cap; spr "[%s] flows to value, but is not weak" (strLoc l)]
    | [], _ -> err ([cap; "0 ref terms flow to value"])
    | l, _  -> err ([cap; "multiple ref terms flow to value";
                     String.concat ", " (List.map prettyStrTT l)])

let singleStrongRefTermOf cap g t = singleRefTermOf ~strong:(Some true) cap g t
let singleWeakRefTermOf cap g t   = singleRefTermOf ~strong:(Some false) cap g t

let ensureSafeWeakRef cap g t =
  failwith "ensureSafeWeakRef"
(*
  let safe = TRefinement ("v", PNot (PEq (theV, aNull))) in
  Sub.checkTypes cap g TypeTerms.empty t safe
*)

let arrayTermsOf g = function
  | THasTyp([UArray(t)],_) ->
      (* let _ = Log.log1 "don't call extract [Array(%s)]\n" (strTyp t) in *)
      [UArray t]
  | t ->
      (* Log.log1 "call extract arrayTermsOf [%s]\n" (prettyStrTyp t); *)
      let filter = function UArray _ -> true | _ -> false in
      TypeTerms.elements (Sub.mustFlow g t ~filter)

let arrowTermsOf g t =
  match t with
    | THasTyp(us,_) ->
        (* this means that if there are any type terms at the top-level of
           the type, return them. not _also_ considering the refinement to
           see if that leads to more must flow boxes. *)
        (* let _ = Log.log1 "don't call extract EApp [%s]\n" (prettyStrTyp t) in *)
        us
    | _ ->
        (* let _ = Log.log1 "call extract EApp [%s]\n" (prettyStrTyp t) in *)
        let filter = function UArrow _ -> true | _ -> false in
        TypeTerms.elements (Sub.mustFlow g t ~filter)


(**** Join for T-If ***********************************************************)

let joinVal v v1 v2 =
  let x = freshVar "join" in
  let t = ty (pIte (pGuard v true) (eq theV (WVal v1)) (eq theV (WVal v2))) in
  (x, t)

(* TODO once i add existential locations, don't allow any locations to be
   dropped *)
let joinHeapEnvs v (hs1,cs1) (hs2,cs2) =
  if hs1 <> hs2 then failwith "joinHeapEnvs: different heap variables";
  let (l,cs) =
    List.fold_left (fun (acc1,acc2) (loc,hc) ->
      match hc, findCell loc ([],cs2) with
        | HEWeakTok(ts1), Some(HEWeakTok(ts2)) when ts1 = ts2 ->
            (acc1, (loc, HEWeakTok ts1) :: acc2)
        | HEConc(v1), Some(HEConc(v2)) when v1 = v2 ->
            (acc1, (loc, HEConc v1) :: acc2)
        | HEConcObj(v1,loc'), Some(HEConcObj(v2,_)) when v1 = v2 ->
            (acc1, (loc, HEConcObj (v1, loc')) :: acc2)
        | HEConc(v1), Some(HEConc(v2)) ->
            let (x,t) = joinVal v v1 v2 in
            ((x,t) :: acc1, (loc, HEConc (vVar x)) :: acc2)
        | HEConcObj(v1,loc'), Some(HEConcObj(v2,loc'')) when loc' = loc'' ->
            let (x,t) = joinVal v v1 v2 in
            ((x,t) :: acc1, (loc, HEConcObj (vVar x, loc')) :: acc2)
        | _ ->
            (acc1, acc2)
    ) ([],[]) cs1
  in
  (l, (hs1,cs))

let joinTypes v t1 t2 =
  let (l1,s1) = stripExists t1 in
  let (l2,s2) = stripExists t2 in
  let x = freshVar "_ret_if" in
  let p = pIte (pGuard v true) (applyTyp s1 (wVar x)) (applyTyp s2 (wVar x)) in
  (l1 @ l2, TRefinement(x,p))

let joinWorlds v (t1,heap1) (t2,heap2) : typ * heapenv =
  let (l1,s) = joinTypes v t1 t2 in
  let (l2,h) = joinHeapEnvs v heap1 heap2 in
  (mkExists s (l1 @ l2), h)

(*
let joinWorlds v w1 w2 =
  let w = joinWorlds v w1 w2 in
  Log.log0 "joinWorlds\n\n";
  Log.log1 "%s\n\n" (prettyStr strWorld w1);
  Log.log1 "%s\n\n" (prettyStr strWorld w2);
  Log.log1 "%s\n\n" (prettyStr strWorld w);
  w
*)
  

(***** TC application helpers *************************************************)

let isArrow = function
  | TRefinement(x,PUn(HasTyp(y,UArrow(arr)))) when y = wVar x -> Some arr
(*
  | THasTyp(UArr(arr)) -> Some arr
*)
  | THasTyp([UArrow(arr)],PTru) -> Some arr
  | _ -> None

let isArrows t =
  match isArrow t, t with
    | Some(arr), _ -> Some [arr]
    | None, TRefinement(x,PConn("and",ps)) ->
        List.fold_left (fun acc p ->
          match acc, p with
            | Some(l), PUn(HasTyp(y,UArrow(arr))) when y = wVar x -> Some(arr::l)
            | _ -> None
        ) (Some []) ps
    | _, THasTyp(us,PTru) ->
        List.fold_left (fun acc u ->
          match acc, u with
            | Some(l), UArrow(arr) -> Some(arr::l)
            | _ -> None
        ) (Some []) us
    | _ -> None

let frameIsNonArrowType (_,_,(t,h)) =
  match isArrows t with
    | None   -> true
    | Some _ -> false

let destructNonArrowTypeFrame (_,_,(t,h)) =
  match isArrows t with
    | None   -> t
    | Some _ -> failwith "destructNonArrowTypeFrame: impossible"

type app_rule_result =
  | AppOk   of (typ * heapenv)
  | AppFail of string list

(* TODO 8/15 what is depTupleSubst and heapDepTupleSubst?
   can/should these be factored somewhere else?
   now with heap envs, can't heapDepTupleSubst select path from
   corresponding values, like depTupleSubst? *)

(* for each dep tuple binder x in t, adding a mapping from x to w.path,
   where path is the path to the x binder *)
let depTupleSubst t w =
  let rec foo path acc = function
    | TTuple(l) ->
        Utils.fold_left_i (fun acc (x,t) i ->
          let path = sel path (wProj i) in
          let acc = foo path acc t in
          (x, path) :: acc
        ) acc l
(*
    | TNonNull(t) | TMaybeNull(t) -> failwith "depTupleSubst: null"
*)
    | TNonNull(t) -> failwith "depTupleSubst: nonnull"
    (* TODO ok to just recurse inside? *)
    | TMaybeNull(t) -> foo path acc t
    | _ -> acc
  in
  let subst = foo w [] t in
(*
  Log.log1 "depTupleSubst [%s]\n" (prettyStrTyp t);
  List.iter (fun (x,w) -> Log.log2 "ravi %s |-> %s\n" x (prettyStrWal w)) subst;
*)
  subst

let heapDepTupleSubst (_,cs) =
  let rec foo path acc = function
    | TTuple(l) ->
        Utils.fold_left_i (fun acc (x,t) i ->
          let path = sel path (wProj i) in
          let acc = foo path acc t in
          (x, path) :: acc
        ) acc l
    | TNonNull(t) -> failwith "heapDepTupleSubst: nonnull"
    (* TODO ok to just recurse inside? *)
    | TMaybeNull(t) -> foo path acc t
    | _ -> acc
  in
  let subst =
    List.fold_left (fun acc -> function
      | (_,HConc(None,s)) | (_,HConcObj(None,s,_)) -> acc (* TODO 8/14 *)
      | (_,HConc(Some(x),s)) | (_,HConcObj(Some(x),s,_)) -> foo (wVar x) acc s
      | _ -> acc (* TODO 3/9 *)
    ) [] cs
  in
(*
  Log.log0 "heapDepTupleSubst\n";
  List.iter (fun (x,w) -> Log.log2 "ravi %s |-> %s\n" x (prettyStrWal w)) subst;
*)
  subst


(***** Heap parameter inference ***********************************************)

let oc_local_inf = open_out (Settings.out_dir ^ "local-inf.txt")

let inferHeapParam cap curHeapEnv = function
  | [x], ([x'],cs1) when x = x' ->
      let (hs,cs) = curHeapEnv in
      let cs =
        List.fold_left (fun acc (l,x) ->
          if List.mem_assoc l cs1 then acc
          else match x with
            | HEWeakTok(x) -> (l, HWeakTok x) :: acc
            | HEConc(v) -> (l, HConc (None, valToSingleton v)) :: acc
            | HEConcObj(v,l') ->
                (l, HConcObj (None, valToSingleton v, l')) :: acc
        ) [] cs
      in Some (hs, cs)
  | _ -> None

let inferHeapParam cap curHeapEnv hForm e11 =
  fpr oc_local_inf "\n%s\n\n" cap;
  match inferHeapParam cap curHeapEnv (hForm,e11) with
    | None -> None
    | Some(e) -> begin
        fpr oc_local_inf "  heap formal: %s\n" (prettyStrHeap e11);
        fpr oc_local_inf "  inferred heap: %s\n " (prettyStrHeap e);
        Some e
      end


(***** Type/loc parameter inference *******************************************)

(** This is tailored to inferring location parameters and type variables for
    object and array primitive operations. Both the Ref and Array type term
    constructors are invariant in their parameter, so the greedy choice
    (e.g. unification) is guaranteed to be good.

    The entry point is

      inferTypLocParams g tForms lForms tForm hForm tActs lActs vAct hAct

 ** Step 1: Find type and value tuples

      Want to collect a tuple vTup of value arguments passed in, and a tuple tTup
      of type arguments expected, so that we can compare each vTup[i] to tTup[i]
      to infer missing arguments. There are three cases for function
      types/calls from desugaring:
                                    i.   direct call to a !D primitive
                                    ii.  DJS simple call
                                    iii. DJS method call

      Case i:    tForm = [x1:T1, ..., xn:Tn]

        The argument vAct must be a tuple with n values.

      Case ii:   tForm = [arguments:Ref(Largs)]

        The last location parameter is Largs. Look for Largs in the heap
        formal, and it should be a tuple of types tTup. The last (and only
        location) argument should be argsArray. Look for this location
        in the heap and use its value as the vTup.
 
      Case iii:  tForm = [this:Tthis, arguments:Targuments]

        Just like the previous case, but add Tthis to the front of the
        type tuple, and the this argument to the front of the value tuple.

 ** Step 2: Inferring location parameters for location formals lForms

      Process lForms in increasing order.

      For each Li:

      - if    there is some tTup[j] = Ref(Li)
        and   G => vTup[j] :: Ref(l)
        then  add Li |-> l to the location substitution

      - if    there is some (L |-> (_:_, Li)) in the heap formal
        and   L |-> l is part of location substitution
        and   (l |-> (_:_, l')) is in the heap actual
        then  add Li |-> l' to the location substitution

      Notice that for a function that takes a reference to L1, and the
      heap constraint for L1 links to L2, then the location parameter L1
      must appear in lForms before L2. This is how all the primitives
      are written anyway, since it's intuitive.

 ** Step 3: Inferring type parameters for type formals tForms

      For each Ai:

      - if    there is some Lj s.t. (Lj |-> (_:Arr(A), _))
        and   the location substitution maps Lj to l
        and   (l |-> (a:_, _)) is in the heap actual
        and   G => a :: Arr(T)
        then  add A |-> T to the type substitution

      Note that the first step looks for Arr(A) syntactically, which is
      how all the primitives are written. Might need to make this more
      general later.
*)

let _strTyps ts = String.concat "," (List.map strTyp ts)
let _strVals vs = String.concat "," (List.map prettyStrVal vs)

let isIntOfString s =
  try Some (int_of_string s) with Failure _ -> None

(* try to match v as a tuple dictionary, that is, a dictionary with
   fields "0" through "n" in order without any duplicates. *)
let isValueTuple v =
  let rec foo acc n = function
    | {value=VEmpty} ->
        Some acc (* no need to rev, since outermost starts with "n" *)
    | {value=VExtend(v1,{value=VBase(Str(sn))},v3)} ->
        (match isIntOfString sn with
           | Some(n') when n = n' -> foo (v3::acc) (n-1) v1
           | None -> None)
    | _ -> None
  in
  match v with
    | {value=VExtend(_,{value=VBase(Str(sn))},_)} ->
        (match isIntOfString sn with Some(n) -> foo [] n v | None -> None)
    | {value=VEmpty} -> Some []
    | _ -> None

let findActualFromRefValue g lVar tTup vTup =
  let rec foo i = function
    (* 3/14 added the MaybeNull case since the objects.dref primitives
       now take nullable strong references *)
    | (THasTyp([URef(LocVar(lVar'))],_) :: ts)
    | (TMaybeNull(THasTyp([URef(LocVar(lVar'))],_)) :: ts) when lVar = lVar' ->
        if i >= List.length vTup then None
        else
          let vi = List.nth vTup i in
          begin match refTermsOf g (selfifyVal g vi) with
            | [URef(lAct)] ->
                let _ = fpr oc_local_inf "  %s |-> %s\n" lVar (strLoc lAct) in
                Some lAct
            (* 3/31 might want to check case with multiple ref terms *)
            | _ -> foo (i+1) ts
          end
    | _ :: ts -> foo (i+1) ts
    | [] -> None
  in
  foo 0 tTup

let findActualFromProtoLink locSubst lVar hForm hAct =
  let rec foo = function
    | (LocVar lVar', HConcObj (_, _, LocVar x)) :: cs when lVar = x ->
        if not (List.mem_assoc lVar' locSubst) then foo cs
        else begin match List.assoc lVar' locSubst with
          | None -> None
          | Some(lAct') ->
              if not (List.mem_assoc lAct' (snd hAct)) then foo cs
              else begin match List.assoc lAct' (snd hAct) with
                | HConcObj(_,_,lAct) ->
                    let _ = fpr oc_local_inf "  %s |-> %s\n" lVar (strLoc lAct) in
                    Some lAct
                | _ -> None
              end
        end
    | _ :: cs -> foo cs
    | []      -> None
  in
  foo (snd hForm)

let findArrayActual g tVar locSubst hForm hAct =
  let rec foo = function
(*
    | (LocVar lVar, HConc (_, THasTyp (UArray (THasTyp (UVar x))))) :: cs
    | (LocVar lVar, HConcObj (_, THasTyp (UArray (THasTyp (UVar x))), _)) :: cs
*)
    | (LocVar lVar, HConc (_, THasTyp ([UArray (THasTyp ([UVar x], _))], _))) :: cs
    | (LocVar lVar, HConcObj (_, THasTyp ([UArray (THasTyp ([UVar x], _))], _), _)) :: cs
      when tVar = x ->
(*
        let _ = pr "ravi %s" (strHeap hForm) in
*)
        if not (List.mem_assoc lVar locSubst) then foo cs
        else begin match List.assoc lVar locSubst with
          | None -> foo cs
          | Some(lAct) ->
              if not (List.mem_assoc lAct (snd hAct)) then foo cs
              else begin match List.assoc lAct (snd hAct) with
                | HConc(None,_) | HConcObj(None,_,_) ->
                    failwith "findArrayActual none"
                | HConc(Some(a),_)
                | HConcObj(Some(a),_,_) ->
(*
                    (match arrayTermsOf g (ty (PEq (theV, wVar a))) with
*)
                    (match arrayTermsOf g (selfifyVar g a) with
                       | [UArray(t)] -> Some t
                       (* 3/31 Arr({v|v != undef}) and Arr({v'|v' != undef}) *)
                       | UArray(t)::_ -> Some t
                       | _           -> foo cs)
                | HWeakTok _ ->
                    foo cs
              end
        end
    | _ :: cs -> foo cs
(*
    | c :: cs -> let _ = pr "didn't match %s" (prettyStrHeap ([],[c])) in foo cs
*)
    | []      -> None
  in
  foo (snd hForm)

let steps2and3 g tForms lForms vFormTup hForm vActTup hAct =

  fpr oc_local_inf "  vFormTup: [%s]\n" (_strTyps (List.map snd vFormTup));
  fpr oc_local_inf "  vActTup:  [%s]\n" (_strVals vActTup);

  (* Step 2 *)
  let locSubst =
    List.fold_left (fun subst lVar ->
      let maybeActual = 
        match findActualFromRefValue g lVar (List.map snd vFormTup) vActTup with
          | None       -> findActualFromProtoLink subst lVar hForm hAct
          | Some(lact) -> Some lact in
      ((lVar,maybeActual)::subst)
    ) [] lForms in

  let lActsOpt =
    List.fold_left (fun acc (_,lActOpt) ->
      match acc, lActOpt with
        | Some(l), Some(lAct) -> Some (lAct::l)
        | _                   -> None
    ) (Some []) locSubst in

  begin match lActsOpt with
    | None -> ()
    | Some(lActs) ->
        fpr oc_local_inf "  inferred all loc acts: [%s]\n" (strLocs lActs)
  end;

  (* Step 3 *)
  let tActsOpt =
    match tForms with
      | []     -> Some []
      | [tVar] -> (match findArrayActual g tVar locSubst hForm hAct with
                     | Some(tAct) -> Some [tAct]
                     | None       -> None)
      | _      -> None (* generalize the case for one to all tparams *) in

  (* don't need to reverse lActs, since the two folds reversed it twice *)
  match tActsOpt, lActsOpt with
    | Some(l1), Some(l2) -> begin
        fpr oc_local_inf "  inferred all typ acts: [%s]\n" (_strTyps l1);
        Some (l1, l2)
      end
    | _ -> None

let inferTypLocParams cap g tForms lForms tForm hForm tActs lActs vAct hAct =
  if List.length tActs <> 0 then None
  else if List.length lActs = List.length lForms then None
  else begin
    fpr oc_local_inf "\n%s\n\n" cap;
    match tForm with
      | TTuple([("arguments",t)]) -> begin
          match t, lActs with
(*
            | THasTyp(URef(lArgsForm)), [lArgsAct] ->
*)
            | THasTyp([URef(lArgsForm)],_), [lArgsAct] ->
                let (lForms,_) = Utils.longHeadShortTail lForms in
                if not (List.mem_assoc lArgsForm (snd hForm)) then None
                else if not (List.mem_assoc lArgsAct (snd hAct)) then None
                else begin match List.assoc lArgsAct (snd hAct),
                                 List.assoc lArgsForm (snd hForm) with
                  | HConc(_,TRefinement("v",PEq(WVal({value=VVar"v"}),WVal(v)))),
                    HConc(_,TTuple(vFormTup)) -> begin
                      match isValueTuple v with
                        | None -> None
                        | Some(vActTup) -> begin
                            match steps2and3 g tForms lForms vFormTup hForm
                                             vActTup hAct with
                              | Some(ts,ls) -> Some (ts, ls @ [lArgsAct])
                              | None        -> None
                          end
                    end
                  | _ -> None
                end
            | _ -> None
        end
      (* copied from above case, and doing a bit extra to process the this
         formal and actual *)
      | TTuple([("this",tThis);("arguments",t)]) -> begin
          match t, lActs with
(*
            | THasTyp(URef(lArgsForm)), [lArgsAct] ->
*)
            | THasTyp([URef(lArgsForm)],_), [lArgsAct] ->
                let (lForms,_) = Utils.longHeadShortTail lForms in
                if not (List.mem_assoc lArgsForm (snd hForm)) then None
                else if not (List.mem_assoc lArgsAct (snd hAct)) then None
                else begin match List.assoc lArgsAct (snd hAct),
                                 List.assoc lArgsForm (snd hForm),
                                 isValueTuple vAct with
                  | HConc(_,TRefinement("v",PEq(WVal({value=VVar"v"}),WVal(v)))),
                    HConc(_,TTuple(vFormTup)),
                    Some([vThis;_]) -> begin
                      match isValueTuple v with
                        | None -> None
                        | Some(vActTup) -> begin
                            let vFormTup = ("this",tThis) :: vFormTup in
                            let vActTup = vThis :: vActTup in
                            match steps2and3 g tForms lForms vFormTup hForm
                                             vActTup hAct with
                              | Some(ts,ls) -> Some (ts, ls @ [lArgsAct])
                              | None        -> None
                          end
                    end
                  | _ -> None
                end
            | _ -> None
        end
      | TTuple(vFormTup) -> begin
          match isValueTuple vAct with
            | None -> None
            | Some(vActTup) ->
                steps2and3 g tForms lForms vFormTup hForm vActTup hAct
        end
      | _ -> None
  end

(* TODO 8/14 need to update for heapenv *)
let inferTypLocParams cap g tForms lForms tForm hForm tActs lActs vAct hAct =
  None


(***** Bidirectional type checking ********************************************)

(***** Initial trivial checks *****)

let rec tsVal g h e =
  if !Settings.doFalseChecks && Zzz.falseIsProvable "tsVal" then tyFls
  else tsVal_ g h e

and tsExp g h e : typ * heapenv =
  if !Settings.doFalseChecks && Zzz.falseIsProvable "tsExp" then (tyFls, h)
  else tsExp_ g h e

and tcVal g h s e =
  if !Settings.doFalseChecks && Zzz.falseIsProvable "tcVal" then ()
  else tcVal_ g h s e

and tcExp g h (w: world) e =
  if !Settings.doFalseChecks && Zzz.falseIsProvable "tcExp" then ()
  else tcExp_ g h w e


(***** Value type synthesis ***************************************************)

and tsVal_ g h = function

  (* 3/15 adding v::Null back in *)
  | {value=VBase(Null)} -> tyNull

  | {value=VVar("__skolem__")} -> tyNum

  | {value=VBase(Str("no source file"))} when !Settings.marshalOutEnv -> begin
      let oc_env = open_out_bin (Settings.out_dir ^ "env.env") in
      Marshal.to_channel oc_env (g,h) [];
      Utils.copyFile
        (Settings.out_dir ^ "queries.lisp") (Settings.out_dir ^ "env.lisp");
      (* TODO need to marshal other state too... *)
      ty (PEq (theV, wStr "no source file"))
    end

  | ({value=VBase _} as v) | ({value=VEmpty} as v) -> ty (PEq (theV, WVal v))

  (* TODO any benefit to using upd instead of VExtend? *)
  | ({value=VExtend(v1,v2,v3)} as v) -> begin
      tcVal g h tyDict v1;
      tcVal g h tyStr v2;
      ignore (tsVal g h v3);
      ty (PEq (theV, WVal v))
    end

  | {value=VVar(x)} -> selfifyVar g x

  | {value=VFun _} -> failwith "ts VFun"

  | {value=VArray(tInv,vs)} -> begin
      List.iter (tcVal g h tInv) vs;
      let n = List.length vs in
      let ps = 
        (* eq (tag theV) (wStr tagArray) :: *)
        packed theV :: PEq (arrlen theV, wInt n)
        :: Utils.map_i (fun vi i -> PEq (sel theV (wInt i), WVal vi)) vs in
      THasTyp ([UArray tInv], pAnd ps)
    end

(*
  | VArray(t,vs) -> begin
      let (tInv,q) =
        match t with
          | THasTyp([UArray(tInv)],q) -> (tInv, q)
          (* TODO should be able to remove this once tyArrayTuple issue
             is fixed *)
          | TRefinement("v",PConn("and",
              PUn(HasTyp(WVal(VVar"v"),UArray(tInv)))::ps)) -> (tInv, pAnd ps)
          | _ -> err [spr "TS-Array: [%s] bad shape" (prettyStrTyp t)] in
      List.iter (tcVal g h tInv) vs;
      let n = List.length vs in
(*
      ty (pAnd (
        hastyp theV (UArray t)
        :: packed theV :: PEq (arrlen theV, wInt n)
        :: Utils.map_i (fun vi i -> PEq (sel theV (wInt i), WVal vi)) vs))
*)
(* 3/12
*)
      let ps = 
        (* eq (tag theV) (wStr tagArray) :: *)
        packed theV :: PEq (arrlen theV, wInt n)
        :: Utils.map_i (fun vi i -> PEq (sel theV (wInt i), WVal vi)) vs in
(* 3/14
      THasTyp ([UArray t], pAnd ps)
*)
      (* TODO shouldn't be able to use q unless prove it somehow *)
      let q = "blah" in
      THasTyp ([UArray tInv], pAnd (ps))
    end
*)


(***** Expression type synthesis **********************************************)

and tsExp_ g h = function

  | EVal(v) -> (tsVal g h v, h)

  | ENewref(l,EVal(v)) ->
      let cap = spr "TS-Newref: %s (%s) in ..." (strLoc l) (prettyStrVal v) in
      begin match findCell l h with
        | Some _ -> err ([cap; spr "location [%s] already bound" (strLoc l)])
        | None ->
            let _ = tsVal g h v in
            let h' = (fst h, snd h @ [(l, HEConc v)]) in
            (tyRef l, h')
      end

  | EDeref(EVal(v)) ->
      let cap = spr "TS-Deref: !(%s)" (prettyStrVal v) in
      let t1 = tsVal g h v in
      let l = singleRefTermOf cap g t1 in
      begin match findCell l h with
        | Some(HEConc(v')) -> (valToSingleton v', h)
        | Some(HEConcObj _) -> err ([cap; "can't deref object location"])
        | Some(HEWeakTok _) -> err ([cap; "can't deref weak location"])
        | None -> err ([cap; spr "unbound loc [%s]" (strLoc l)])
      end

  | ESetref(EVal(v1),EVal(v2)) ->
      let (s1,s2) = (prettyStrVal v1, prettyStrVal v2) in
      let cap = spr "TS-Setref: (%s) := (%s)" s1 s2 in
      let t = tsVal g h v1 in
      let _ = tsVal g h v2 in
      let l = singleRefTermOf cap g t in
      begin match findAndRemoveCell l h with
        | None -> err ([cap; spr "unbound loc [%s]" (strLoc l)])
        | Some(HEConcObj _, _) -> err ([cap; "can't setref object location"])
        | Some(HEWeakTok _, _) -> err ([cap; "can't setref weak location"])
        | Some(HEConc(v), h0) ->
            let h' = (fst h0, snd h0 @ [(l, HEConc v2)]) in
            (valToSingleton v2, h')
      end

  | ENewObj(EVal(v1),l1,EVal(v2),l2) ->
      let cap = spr "TS-NewObj: new (%s, %s, %s, %s)"
        (prettyStrVal v1) (strLoc l1) (prettyStrVal v2) (strLoc l2) in
      begin match findCell l1 h, findCell l2 h with
        | None, Some(HEConcObj _) ->
            let _ = tcVal g h tyDict v1 in
            let _ = tcVal g h (tyRef l2) v2 in
            let h' = (fst h, snd h @ [l1, HEConcObj (v1, l2)]) in
            (tyRef l1, h')
        | None, Some _ -> err [cap; spr "loc [%s] isn't a conc obj" (strLoc l2)]
        | None, None -> err [cap; spr "loc [%s] isn't bound" (strLoc l2)]
        | Some _, _ -> err [cap; spr "loc [%s] already bound" (strLoc l1)]
      end

  | EApp(l,EVal(v1),EVal(v2)) -> begin
      let (s1,s2) = (prettyStrVal v1, prettyStrVal v2) in
      let cap = spr "TS-App: [...] (%s) (%s)" s1 s2 in
      let t1 = tsVal g h v1 in
      let boxes = arrowTermsOf g t1 in
      tsELetAppTryBoxes cap g h l v1 v2 boxes
    end

(*
  | ELet(x,Some(frame),e1,e2) -> begin
      let ruleName = "TS-Let-Ann" in
      let cap = spr "%s: let %s = ..." ruleName x in
      Wf.frame cap g frame;
      Zzz.pushScope ();
      let (s1,h1) = applyFrame h frame in
      tcExp g h (s1,h1) e1;
      Zzz.popScope ();
      let (bindings,h1) = heapEnvOfHeap h1 in
      let (m,g1) = tcAddManyBindings bindings g in
      if h1 <> h then printHeapEnv h1;
      let (n,g1) = tcAddBinding g x s1 in
      let (s2,h2) = tsExp g1 h1 e2 in
      tcRemoveBindingN (n + m);
      finishLet (spr "%s: let %s = ..." ruleName x) g x [(x,s1)] (s2,h2)
*)

  (* 8/20: split TS-Let-Ann into two cases, depending on whether the frame
     annotation is for a function type or not. *)

  | ELet(x,Some(frame),e1,e2) when frameIsNonArrowType frame -> begin
      let ruleName = "TS-Let-Ann-Not-Arrow" in
      let cap = spr "%s: let %s = ..." ruleName x in
      let (s1,h1) = Zzz.inNewScope (fun () -> tsExp g h e1) in
      let (s1,h1) = elimSingletonExistentials (s1,h1) in
      let tGoal = destructNonArrowTypeFrame frame in
      Sub.types cap g s1 tGoal;
      if h1 <> h then printHeapEnv h1;
      (* synthesizing x:s1, _not_ the goal tGoal, since need to bring all the
         binders in scope, since they may refered to in h1. so the tGoal
         annotation is simply a check rather than an abstraction. *)
      let (n,g1) = tcAddBinding g x s1 in
      Log.log2 "%s :: %s\n"
        (String.make (String.length x) ' ') (prettyStrTyp tGoal);
      let (s2,h2) = tsExp g1 h1 e2 in
      tcRemoveBindingN n;
      finishLet cap g x [(x,s1)] (s2,h2)
    end

  | ELet(x,Some(frame),e1,e2) (* when not (frameIsNonArrowType frame) *) -> begin
      let ruleName = "TS-Let-Ann-Arrow" in
      let cap = spr "%s: let %s = ..." ruleName x in
      let (s1,h1) = applyFrame h frame in
      Zzz.inNewScope (fun () -> tcExp g h (s1,h1) e1);
      let (bindings,h1) = heapEnvOfHeap h1 in
      let (m,g1) = tcAddManyBindings bindings g in
      if h1 <> h then printHeapEnv h1;
      let (n,g1) = tcAddBinding g x s1 in
      let (s2,h2) = tsExp g1 h1 e2 in
      tcRemoveBindingN (n + m);
      finishLet cap g x [(x,s1)] (s2,h2)
    end

  | ELet(x,None,e1,e2) -> begin
      let ruleName = "TS-Let-Bare" in
      let cap = spr "%s: let %s = ..." ruleName x in
      let (s1,h1) = Zzz.inNewScope (fun () -> tsExp g h e1) in
      let (s1,h1) = elimSingletonExistentials (s1,h1) in
      let (l1,s1) = stripExists s1 in
      if h1 <> h then printHeapEnv h1;
      let (m,g1) = tcAddManyBindings l1 g in
      let (n,g1) = tcAddBinding g1 x s1 in
      let (s2,h2) = tsExp g1 h1 e2 in
      tcRemoveBindingN (m + n);
      finishLet cap g x (l1 @ [(x,s1)]) (s2,h2)
    end

  | EIf(EVal(v),e1,e2) -> begin 
      (* TODO check if false is provable? *)
      tcVal g h tyAny v;
      let (s1,h1) = Zzz.inNewScope (fun () ->
        Zzz.assertFormula (pTruthy (WVal v)); tsExp g h e1) in
      let (s2,h2) = Zzz.inNewScope (fun () ->
        Zzz.assertFormula (pFalsy (WVal v)); tsExp g h e2) in
      joinWorlds v (s1,h1) (s2,h2)
    end

  | EExtern(x,s,e) -> begin
      if !depth > 0 then err [spr "extern [%s] not at top-level" x];
      let s = ParseUtils.undoIntersectionHack g s in
      Wf.typ (spr "ts extern %s" x) g s;
      let (n,g1) = tcAddBinding g x s in
      let (s2,h2) = tsExp g1 h e in
      tcRemoveBindingN n;
      finishLet (spr "%s: let %s = ..." "TS-Extern" x) g x [(x,s)] (s2,h2)
    end

  | EWeak((m,t,l),e) -> begin
      if isStrongLoc m then err ["TS-EWeak: location should be weak"];
      let g = WeakLoc (m, t, l) :: g in
      Wf.typ "EWeak" g t;
      let h = (fst h, (m, HEWeakTok Frzn) :: snd h) in
      tsExp g h e
    end

  | ETcFail(s,e) ->
      failwith "ts tcfail"
(*
      let fail =
        try let _ = tsExp g h e in false
        with Tc_error _ -> true in
      if fail
        then (STyp tyAny, h)
        else err (spr "ts ETcFail: [\"%s\"] should have failed" s)
*)

  | EAs(s,e,f) -> begin
      failwith "tsexp eas heapenv"
(*
      let w = applyFrame h f in
      tcExp g h w (EAsW(s,e,w));
      w
*)
    end

  | EAsW(s,e,w) -> begin
      Wf.world (spr "TS-EAsW: %s" s) g w;
      let (tGoal,hGoal) = freshenWorld w in
      tcExp g h (tGoal,hGoal) e;
      let (binders,h) = heapEnvOfHeap hGoal in
      (* TODO use a version of mkExists that adds dummy binders first,
         since binders can mutually refer to each other? *)
      (mkExists tGoal binders, h)
    end

  | ELabel(x,e) -> failwith "TS-Label: need a goal"

  (* TODO 9/25 revisit *)
  | EBreak(x,EVal(v)) ->
      let cap = spr "TS-Break: break %s (%s)" x (prettyStrVal v) in
      let lblBinding =
        try List.find (function Lbl(y,_) -> x = y | _ -> false) g
        with Not_found -> err [cap; "label not found"] in
      begin match lblBinding with
        | Lbl(_,Some(tGoal,hGoal)) -> begin
            tcVal g h tGoal v;
            Zzz.queryRoot := "TS-Break";
            ignore (Sub.heapSat cap g h hGoal);
            (tyFls, h)
          end
        | _ -> err [cap; "no goal for label"]
      end

  | EFreeze(m,ts,EVal(v)) ->
      let cap = spr "ts EFreeze: [%s] [%s] [%s]"
        (strLoc m) (strThawState ts) (prettyStrVal v) in
      let _ = if not (isWeakLoc m) then err [cap; "location isn't weak"] in
      let (tFrzn,l') = findWeakLoc g m in
      begin match findAndRemoveCell m h with
        | Some(HEWeakTok(ts'),h0) when ts' = ts ->
            let s = tsVal g h v in
            let l = singleStrongRefTermOf "ts EFreeze" g s in
            begin match findAndRemoveCell l h0 with
              | Some(HEConcObj(v',l''), h1) when l' = l'' ->
                  let _ = Zzz.queryRoot := "TS-Freeze" in
                  let _ = tcVal g h tFrzn v' in
                  let h' = (fst h1, (m, HEWeakTok Frzn) :: snd h1) in
                  (tySafeWeakRef m, h')
              | Some(HEConcObj _, _) ->
                  err [cap; spr "[%s] wrong proto link" (strLoc l)]
              | Some _ -> err [cap; spr "[%s] isn't a strong obj" (strLoc l)]
              | None -> err [cap; spr "[%s] not bound" (strLoc l)]
            end
        | Some(HEWeakTok(ts'),_) ->
            err [cap; spr "different thaw state [%s]" (strThawState ts')]
        | Some _ -> err [cap; "isn't a weaktok constraint"]
        | None -> err [cap; "isn't bound in the heap"]
      end

  | EThaw(l,EVal(v)) ->
      let cap = spr "ts EThaw: [%s] [%s]" (strLoc l) (prettyStrVal v) in
      let _ = if not (isStrongLoc l) then err [cap; "location isn't strong"] in
      begin match findCell l h with
        | Some _ -> err [cap; "already bound"] (* TODO also check DEAD *)
        | None ->
            let t1 = tsVal g h v in
            let m = singleWeakRefTermOf cap g t1 in
            let (tFrzn,l') = findWeakLoc g m in
            begin match findAndRemoveCell m h with
              | Some(HEWeakTok(Frzn), h0) ->
                  let x = freshVar "thaw" in
                  let h' = (fst h0, (m, HEWeakTok (Thwd l))
                                       :: (l, HEConcObj (vVar x, l'))
                                       :: snd h0) in
                  let t = TMaybeNull (tyRef l) in
                  (* this version could be used to more precisely track these
                     references.  but since i'm not interesting in checking for
                     non-nullness, i can use the less precise disjunction.
                     if i do end up going this route, might want a TNullIf sugar
                     form that selfifyVar can look for.
                  let t = ty (pIte (eq (WVal v) wNull)
                                   (eq theV wNull)
                                   (applyTyp (tyRef l) theV)) in
                  *)
                  (TExists (x, tFrzn, t), h')
              | Some(HEWeakTok _, _) -> err [cap; "already thawed"]
              | Some _ -> err [cap; "isn't a weaktok constraint"]
              | None -> err [cap; spr "[%s] location not bound" (strLoc m)]
            end
      end

  | EThrow(EVal(v)) ->
      let _ = tsVal g h v in (tyFls, h)

  | ETryCatch _ -> failwith "ETryCatch"

  | ETryFinally _ -> failwith "ETryFinally"

  | ELoadedSrc(_,e) -> tsExp g h e

  | ELoadSrc(s,_) ->
      failwith (spr "ts ELoadSrc [%s]: should've been expanded" s)

  (* the remaining cases should not make it to type checking, so they indicate
     some failure of parsing or ANFing *)

  | EDict _    -> Anf.badAnf "ts EDict"
  | EFun _     -> Anf.badAnf "ts EFun"
  | EIf _      -> Anf.badAnf "ts EIf"
  | EApp _     -> Anf.badAnf "ts EApp"
  | ENewref _  -> Anf.badAnf "ts ENewref"
  | EDeref _   -> Anf.badAnf "ts EDeref"
  | ESetref _  -> Anf.badAnf "ts ESetref"
  | EBreak _   -> Anf.badAnf "ts EBreak"
  | EThrow _   -> Anf.badAnf "ts EThrow"
  | EFreeze _  -> Anf.badAnf "ts EFreeze"
  | EThaw _    -> Anf.badAnf "ts EThaw"

and tsELetAppTryBoxes cap g curHeap (tActs,lActs,hActs) v1 v2 boxes =

  let checkLength s l1 l2 s2 =
    let (n1,n2) = (List.length l1, List.length l2) in
    if n1 <> n2 then
      err [cap; spr "expected %d %s args but got %d %s" n1 s n2 s2] in

  let tryOne ((tForms,lForms,hForms),y,t11,e11,t12,e12) =

    let (tActs0,lActs0) = (tActs, lActs) in

    let ((tActs,lActs),sInf) =
      match inferTypLocParams cap g tForms lForms t11 e11
                              tActs0 lActs0 v2 curHeap with
        | Some(ts,ls) -> ((ts, ls), "with help from local inference")
        | None        -> ((tActs0, lActs0), "without help from local inference") in

    (* at some point, might want to rewrite the input program with
       inferred instantiations *)
(*
    if (tActs,lActs) <> (tActs0,lActs0) then begin
      let foo (ts,ls) =
        spr "[%s; %s]" (String.concat "," (List.map strTyp ts))
                       (String.concat "," (List.map strLoc ls)) in
      Log.log0 "local inference succeeded:\n";
      Log.log1 "  before : %s\n" (foo (tActs0,lActs0));
      Log.log1 "  after  : %s\n" (foo (tActs,lActs));
    end;
*)

    (* check well-formedness of type and loc args *)
    checkLength "type" tForms tActs sInf;
    checkLength "loc" lForms lActs sInf;
    (match Utils.someDupe lActs with
       | None    -> ()
       | Some(l) -> err [cap; spr "duplicate loc arg: %s" (strLoc l)]);
    let tSubst = Utils.safeCombine "app tSubst" tForms tActs in
    let lSubst = Utils.safeCombine "app lSubst" lForms lActs in

    (* instantiate input world with type and loc args *)
    let t11 = substTyp ([],tSubst,lSubst,[]) t11 in
    let e11 = substHeap ([],tSubst,lSubst,[]) e11 in

    (* infer missing heap instantiation, once loc args have been substituted. *)
    let (hActs,sInf) =
      if hActs <> [] then (hActs, "heap actuals were supplied") else
        match inferHeapParam cap curHeap hForms e11 with
          | Some(e) -> ([e], "heap actuals were inferred")
          | None    -> ([], "heap actuals could not be inferred") in

    checkLength "heap" hForms hActs sInf;
    let hSubst = Utils.safeCombine "app hSubst" hForms hActs in

    (* instantiate input with heap args and expand pre-formulas to formulas *)
    let t11 = t11 |> substTyp ([],[],[],hSubst) |> expandPreTyp in
    let e11 = e11 |> substHeap ([],[],[],hSubst) |> expandPreHeap in
    Wf.heap "e11 after instantiation" g e11;

    (* TODO 8/17 removed argSubst/heapPreSubst from e11 *)

    Zzz.queryRoot := "TS-App";
    let argSubst = (y, WVal v2) :: (depTupleSubst t11 (WVal v2)) in
    let heapSubst = Sub.heapSat cap g curHeap e11 in
    tcVal g curHeap t11 v2;

    (* instantiate output world with poly args and binder substitution *)
    (* need to freshen after the argument heap binders have been substituted
       into return world. TODO really, why? should be able to do it right away... *)
    let polySubst = ([],tSubst,lSubst,hSubst) in
    let valueSubst = (argSubst @ heapSubst,[],[],[]) in
    let (t12,e12) = (substTyp polySubst t12, substHeap polySubst e12) in
(*
    let (t12,e12) = (substTyp heapPreSubst t12, substHeap heapPreSubst e12) in
*)
    let (t12,e12) = (substTyp valueSubst t12, substHeap valueSubst e12) in
    let (t12,e12) = freshenWorld (t12,e12) in
    let (t12,e12) = (expandPreTyp t12, expandPreHeap e12) in
    Wf.heap "e12 after instantiation" g e12;

    let (heapBindings,h) = heapEnvOfHeap e12 in
    let (heapBindings,h) = avoidSingletonExistentials (heapBindings,h) in
    let t = mkExists t12 heapBindings in
    AppOk (t, h) in (* end tryOne *)

  let result = (* use the first arrow that type checks the call *)
    Utils.fold_left_i (fun acc u i ->
      let s = prettyStrTT u in
      match acc, u with
        | AppOk _, _ -> acc
        | AppFail(l), UArrow(uarr) -> begin
            try tryOne uarr
            with Tc_error(errList) ->
              AppFail (l @ [spr "\n*** box %d: %s" i s] @ errList)
          end
        | AppFail(l), _ -> AppFail (l @ [spr "box %d isn't an arrow: %s" i s])
    ) (AppFail []) boxes in

  match result with
    | AppOk(t,h) -> (t, h)
    | AppFail(errors) ->
        let n = List.length boxes in
        let s = spr "%d boxes but none type check the call" n in
        Log.printTcErr (cap :: s :: errors)
        (* the buck stops here, instead of raising Tc_error, since otherwise
           get lots of cascading let-bindings *)


(***** Value type conversion **************************************************)

and tcVal_ g h goal = function

  | ({value=VBase _} as v)
  | ({value=VVar _} as v)
  | ({value=VEmpty} as v)
  | ({value=VExtend _} as v) ->
      let s = tsVal g h v in
      let _ = Zzz.queryRoot := "TC-VVal" in
      Sub.types (spr "TC-EVal: %s" (prettyStr strValue v)) g s goal

  | {value=VFun(l,x,None,e)} -> begin
      let ruleName = "TC-Fun-Bare" in
      let g = removeLabels g in
      let checkOne (((ts,ls,hs),y,t1,h1,t2,h2) as arr) =
        let u = UArrow arr in
        Wf.typeTerm (spr "%s: arrow:\n  %s" ruleName (prettyStrTT u)) g u;
        let (ts,ls,hs) =
          if l = ([],[],[]) then (ts,ls,hs)
          else err ["lambda has some params..."]
            (* requiring all params to be missing, since don't want to deal
               with heap prefix vars that get inserted. *)
        in
        let subst = ([(y, wVar x)], [], [], []) in
        let t2 = substTyp subst t2 in
        let h2 = substHeap subst h2 in
        let g = List.fold_left (fun acc x -> TVar(x)::acc) g ts in
        let g = List.fold_left (fun acc x -> LVar(x)::acc) g ls in
        let g = List.fold_left (fun acc x -> HVar(x)::acc) g hs in
        Zzz.inNewScope (fun () ->
          (* since input heap can refer to arg binders, need to process t1 first *)
          let (m,g) = tcAddBinding g x t1 in
          let (bindings,h) = heapEnvOfHeap h1 in
          let (n,g) = tcAddManyBindings bindings g in
          tcExp g h (t2,h2) e;
          tcRemoveBindingN (n + m))
      in
      match isArrows goal with 
        | Some(l) -> List.iter checkOne l
        | None    -> err [spr "%s: goal should be one or more arrows\n  %s"
                            ruleName (prettyStrTyp goal)]
    end

  | {value=VFun(_,_,Some(_),_)} -> err ["TC-Fun-Ann: don't annotate lambdas"]


(***** Expression type conversion *********************************************)

and tcExp_ g h goal = function

  | EVal(v) -> begin
      let (sGoal,hGoal) = goal in
      tcVal g h sGoal v;
      Zzz.queryRoot := "TC-EVal";
      ignore (Sub.heapSat (spr "TC-Val: %s" (prettyStrVal v)) g h hGoal)
    end

  | ENewref(l,EVal(v)) ->
      let cap = spr "TC-Newref: ref (%s, %s)" (strLoc l) (prettyStrVal v) in
      let w = tsExp g h (ENewref(l,EVal(v))) in
      let _ = Zzz.queryRoot := "TC-Newref" in
      ignore (Sub.worldSat cap g w goal)

  | EDeref(EVal(v)) ->
      let w = tsExp g h (EDeref(EVal(v))) in
      let cap = spr "TC-Deref: !(%s)" (prettyStrVal v) in
      let _ = Zzz.queryRoot := "TC-Deref" in
      ignore (Sub.worldSat cap g w goal)

  | ESetref(EVal(v1),EVal(v2)) ->
      let cap = spr "TC-Setref: (%s) := (%s)"
        (prettyStrVal v1) (prettyStrVal v2) in
      let w = tsExp g h (ESetref(EVal(v1),EVal(v2))) in
      let _ = Zzz.queryRoot := "TC-Setref" in
      ignore (Sub.worldSat cap g w goal)

  | ENewObj(EVal(v1),l1,EVal(v2),l2) ->
      let cap = spr "TC-NewObj: new (%s, %s, %s, %s)"
        (prettyStrVal v1) (strLoc l1) (prettyStrVal v2) (strLoc l2) in
      let w = tsExp g h (ENewObj(EVal(v1),l1,EVal(v2),l2)) in
      let _ = Zzz.queryRoot := "TC-NewObj" in
      ignore (Sub.worldSat cap g w goal)

  | EApp(l,EVal(v1),EVal(v2)) ->
      let (s1,s2) = (prettyStrVal v1, prettyStrVal v2) in
      let cap = spr "TC-App: [...] (%s) (%s)" s1 s2 in
      let w = tsExp g h (EApp(l,EVal(v1),EVal(v2))) in
      let _ = Zzz.queryRoot := "TC-App" in
      ignore (Sub.worldSat cap g w goal)

  (* 9/21: special case added when trying to handle ANFed ifs *)
  (* 11/25: added this back in *)
  | ELet(x,None,e1,EVal({value=VVar(x')})) when x = x' ->
      let _ = tcExp g h goal e1 in
      printBinding (x, fst goal)

  (***** all typing rules that use special let-bindings should be above *****)

  | ELet(x,None,e1,e2) ->
      let cap = spr "TC-Let-Bare: let %s = ..." x in
      let e2 = EAsW (cap, e2, goal) in
      let w = tsExp g h (ELet(x,None,e1,e2)) in
      ()

  | ELet(x,Some(a1),e1,e2) ->
      let cap = spr "TC-Let-Ann: let %s = ..." x in
      let e2 = EAsW (cap, e2, goal) in
      let w = tsExp g h (ELet(x,Some(a1),e1,e2)) in
      ()
(*
      let ruleName = "TC-Let-Ann" in
      Wf.frame (spr "%s: let %s = ..." ruleName x) g a1;
      Zzz.pushScope ();
      let (s1,h1) = applyFrame h a1 in
      tcExp g h (s1,h1) e1;
      Zzz.popScope ();
      let (n,g1) = tcAddBinding g h1 x s1 in
      tcExp g1 h1 goal e2;
      tcRemoveBindingN n;
*)

  | EIf(EVal(v),e1,e2) -> begin
      (* TODO check if false is provable? *)
      tcVal g h tyAny v;
      Zzz.inNewScope (fun () ->
        Zzz.assertFormula (pTruthy (WVal v));
        tcExp g h goal e1
      );
      Zzz.inNewScope (fun () ->
        Zzz.assertFormula (pFalsy (WVal v));
        tcExp g h goal e2
      );
    end

  | EWeak(h,e) -> failwith "tc EWeak"

  | EExtern _ -> failwith "tc EExtern"

  | ETcFail(s,e) ->
      let fail =
        try let _ = tcExp g h goal e in false
        with Tc_error _ -> true in
      if fail
        then ()
        else err [spr "tc ETcFail: [\"%s\"] should have failed" s]

  | EAs(_,e,f) -> begin
      failwith "tcexp eas heapenv"
(*
      let w = applyFrame h f in
      tcExp g h w e;
      Zzz.queryRoot := "TC-As";
      ignore (Sub.worlds "TC-EAs" g w goal)
*)
    end

  | EAsW(_,e,w) -> begin
      failwith "tcexp eas heapenv"
(*
      tcExp g h w e;
      Zzz.queryRoot := "TC-AsW";
      ignore (Sub.worlds "TC-EAsW" g w goal)
*)
    end

  | ELabel(x,e) ->
      tcExp (Lbl(x,Some(goal))::g) h goal e

  | EBreak(x,EVal(v)) ->
      let w = tsExp g h (EBreak(x,EVal(v))) in
      let cap = spr "TC-Break: %s" x in
      let _ = Zzz.queryRoot := "TC-Break" in
      ignore (Sub.worldSat cap g w goal)

  | EFreeze _ -> failwith "tc EFreeze"
  | EThaw _ -> failwith "tc EThaw"

  | EThrow _ -> failwith "tc EThrow"
  | ETryCatch _ -> failwith "tc ETryCatch"
  | ETryFinally _ -> failwith "tc ETryFinally"

  (* the remaining cases should not make it to type checking, so they indicate
     some failure of parsing or ANFing *)

  | EDict _    -> Anf.badAnf "tc EDict"
  | EFun _     -> Anf.badAnf "tc EFun"
  | EIf _      -> Anf.badAnf "tc EIf"
  | EApp _     -> Anf.badAnf "tc EApp"
  | ENewref _  -> Anf.badAnf "tc ENewref"
  | EDeref _   -> Anf.badAnf "tc EDeref"
  | ESetref _  -> Anf.badAnf "tc ESetref"


(***** Entry point ************************************************************)

let assertIntegerness e =
  (* TODO might want to also walk inside the types inside expressions, which
     foldExp currently doesn't do *)
  let fE acc = fun _ -> acc in
  let fV acc = function VBase(Int(i)) -> Utils.IntSet.add i acc | _ -> acc in
  let ints = foldExp fE fV Utils.IntSet.empty e in
  Utils.IntSet.iter (fun i -> Zzz.assertFormula (integer (wInt i))) ints;
  ()

let addSkolems g =
  let n = Utils.IdTable.size idSkolems in
  let rec foo acc i =
    if i > n then acc
    else let sk = spr "_skolem_%d" i in
         foo (snd (tcAddBinding acc sk tyNum)) (i+1)
  in
  foo g 1

let initialEnvs () =
  if !Settings.marshalInEnv then
    let ic_env = open_in_bin (Settings.out_dir ^ "env.env") in
    let (g,h) = (Marshal.from_channel ic_env : (env * heapenv)) in
    let g = addSkolems g in
    (g, h)
  else
    let h_init = "H_emp" in
    let g = [HVar h_init] in
    let (_,g) = tcAddBinding g "v" tyAny in
    let g = addSkolems g in
    let (_,g) = tcAddBinding g "dObjectProto" tyEmpty in
    let h = ([h_init], [(lObjectPro, HEConcObj (vVar "dObjectProto", lRoot))]) in
    let _ = printHeapEnv h in
    (g, h)

let typecheck e =
  let oc_num_q = open_out (Settings.out_dir ^ "num-queries.txt") in
  assertIntegerness e;
  let (g,h) = initialEnvs () in
  try begin
    ignore (tsExp g h e);
    Sub.writeCacheStats ();
    Zzz.writeQueryStats ();
    let s = spr "OK! %d queries." !Zzz.queryCount in
    fpr oc_num_q "%d" !Zzz.queryCount;
    Log.log1 "\n%s\n" (Utils.greenString s);
    if not !Log.printToStdout then Printf.printf "\n%s\n" (Utils.greenString s);
  end with Tc_error(s) ->
    Log.printTcErr s

let typecheck e =
  BNstats.time "typecheck" typecheck e

