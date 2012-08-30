
open Lang
open LangUtils


let oc_elim = open_out (Settings.out_dir ^ "elim.txt")

let checkBinder cap g x =
  if List.exists (function Var(y,_) -> x = y | _ -> false) g then
    err [cap; "variable already in scope, so please use a different name."]

let rec checkBinderPat cap g = function
  | PLeaf(x) -> checkBinder cap g x
  | PNode(ps) -> List.iter (checkBinderPat cap g) ps

let baseTypOfBaseVal = function
  | Int _   -> BInt
  | Str _   -> BStr
  | Bool _  -> BBool
  | Undef _ -> BUndef

let rec addPredicate p = function
  | TQuick("v",qt,q)   -> TQuick ("v", qt, pAnd [p;q])
  | TRefinement("v",q) -> TRefinement ("v", pAnd [p;q])
  | TQuick _           -> failwith "addPredicate TQuick"
  | TRefinement _      -> failwith "addPredicate TRefinement"
  | TNonNull(t)        -> TNonNull (addPredicate p t)
  | TMaybeNull(t)      -> TMaybeNull (addPredicate p t)
  | TBaseUnion(l)      -> ty (pAnd [p; applyTyp (TBaseUnion l) theV])
  (* | TExists(x,t1,t2)   -> TExists (x, t1, addPredicate p t2) *)


(**** Selfify *****************************************************************)

(* Rather than blindly returning {v=x}, check if the type of x is a syntactic
   type, and if so, keep that exposed at the top level so that don't need
   as many extractions. *)

let selfifyVar g x =
  try
    let eqX = eq theV (wVar x) in
    begin match List.find (function Var(y,_) -> x = y | _ -> false) g with
      | Var(_,TQuick(y,qt,p)) -> TQuick (y, qt, eqX)
      (* | Var(_,TSelfify(t,p)) -> TSelfify (t, pAnd [eqX; p]) *)
      (* | Var(_,TMaybeNull(t)) -> TSelfify (TMaybeNull(t), eqX) *)
      (* | Var(_,THasTyp(us,p)) -> THasTyp (us, pAnd [eqX; p]) *)
      | _                     -> ty eqX
    end
  with Not_found ->
    err [spr "selfifyVar: var not found: [%s]" x]
  
let selfifyVal g = function
  | {value=VVar(x)} -> selfifyVar g x
  | v               -> valToSingleton v (* ty (PEq (theV, WVal v)) *)


(**** Environment operations **************************************************)

let removeLabels g =
  List.filter (function Lbl _ -> false | _ -> true) g

let printBinding ?(extraBreak=true) ?(isExistential=false) x s =
  if !Settings.printAllTypes || !depth = 0 then begin
    Log.log5 "%s%s%s%s :: %s\n"
      (if extraBreak then "\n" else "") (bigindent ())
      (if isExistential then "Exists " else "") x (strTyp s);
    flush stdout;
  end

let maybePrintHeapEnv hNew hOld =
  if hNew <> hOld && (!Settings.printAllTypes || !depth = 0) then begin
    let ((hs,csNew),(_,csOld)) = (hNew, hOld) in
    (* print heap variables *)
    Log.log2 "\n%s/ %s ++\n" (bigindent ()) (String.concat "++" hs);
    (* print bindings and their relationship to old ones *)
    List.iter (fun (l,hc) ->
      let status =
        if not (List.mem_assoc l csOld) then "+"     (* added *)
        else if hc <> List.assoc l csOld then "*"    (* modified *)
        else " " in                                  (* unchanged *)
      Log.log4 "%s  %s %s |-> %s\n"
        (bigindent ()) status (strLoc l) (strHeapEnvCell hc)
    ) csNew;
    (* print bindings that have been dropped *)
    List.iter (fun (l,hc) ->
      if not (List.mem_assoc l csNew) then
        let status = "-" in                          (* dropped *)
        Log.log3 "%s  %s %s\n"
          (bigindent ()) status (strLoc l)
    ) csOld;
  end

(* TODO *)
let bindingsAreLeftToRight l =
  false

let rec tcAddBinding g x s =
  let g =
    match s with
      | TQuick(_,QTuple(l,_),_) -> (* filtering out those w/o binder *)
          tcAddBindings g
            (List.fold_left (fun acc -> function
               | None, _    -> acc
               | Some(y), t -> (y,t)::acc) [] l)
      | _ -> g in
  let _ = Zzz.addBinding x s in
  let _ = printBinding x s in
  Var(x,s) :: g

and tcAddBindings g l =
  if bindingsAreLeftToRight l then
    List.fold_left (fun g (x,t) -> tcAddBinding g x t) g l
  else
    (* TODO this should be tyAny, but want t stored in g *)
    let g = List.fold_left (fun g (x,t) -> tcAddBinding g x t) g l in
    let _ = List.iter (fun (x,t) -> Zzz.assertFormula (applyTyp t(wVar x))) l in
    g (* might want to print the asserted formulas *)

let rec tcAddBindingPat g p t =
  let sErr = spr "tcAddBindingPat %s %s" (strPat p) (strTyp t) in
  match p, t with
    | PLeaf(x), _ ->
        tcAddBinding g x t
    | PNode(ps), TQuick("v",QTuple(tup,tru),q)
      when q = pTru && List.length ps = List.length tup ->
        List.fold_left (fun g (pi,(yio,si)) ->
          match pi, yio with
            | _, None -> tcAddBindingPat g pi si
            | PLeaf(xi), Some(yi) when xi = yi -> tcAddBinding g xi si
            | _ -> failwith (spr "%s\n%s" sErr (strPat pi))
        ) g (List.combine ps tup)
    | _ ->
        failwith sErr

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

let rec mkExists l s =
  match l with
    | (x,t)::l -> TExists (x, t, mkExists l s)
    | []       -> s

(* Add existentials and check well-formedness. Algorithmic typing should
   always synthesize well-formed types, but doing this as a sanity check. *)
let finishLet cap g y l ((s,h): (prenextyp*heapenv)) : prenextyp * heapenv =
  if Str.string_match (Str.regexp "^end_of" (*"_dref"*)) y 0 then begin
    checkWfHeap := false
  end;
  let w = (mkExists l s, h) in
  (* TODO 8/27/12: figure out why this slows things down so much *)
  if !Settings.checkWfSynthesis && !checkWfHeap then begin
    Wf.prenexTyp (spr "finishLet: %s" cap) g (fst w)
    (* TODO 8/14/12: should also check that the heapenv is well formed *)
  end;
  w

let finishLet = BNstats.time "Tc.finishLet" finishLet

let avoidSingletonExistentials (l,h) =
  List.fold_left (fun (l,h) (x,t) ->
    match maybeValOfSingleton t with
      | Some(v) -> (l, substHeapEnv ([x,WVal(v)],[],[],[]) h)
      | None    -> ((x,t)::l, h)
  ) ([],h) l

(* NOTE For a let-binding of x that synthesizes type Exists x:{v|v=y}. T, would
   like to synthesize T[y/x] instead. But the following function alone is not
   enough since the program may still refer to the variable x, which will get
   substituted into types. So would need to substitute y for x in all
   subsequent types also. So _not_ using this right now. *)
let rec elimSingletonExistentials (t,h) =
  match t with
    | TExists(x,t1,t2) ->
        (match maybeValOfSingleton t1 with
           | Some(v) ->
               let _ = fpr oc_elim "avoided singleton %s\n%s\n%s\n\n"
                 x (strTyp t1) (strHeapEnv h) in
               let subst = ([x,WVal(v)],[],[],[]) in
               elimSingletonExistentials
                 (substPrenexTyp subst t2, substHeapEnv subst h)
           | None ->
               let _ = fpr oc_elim "did not avoid singleton %s\n" x in
               let (t2,h) = elimSingletonExistentials (t2,h) in
               (TExists (x,t1,t2), h))
    | _ -> (t, h)

let stripExists t =
  let rec foo acc = function
    | TExists(x,t,s) -> foo ((x,t)::acc) s
    | Typ(s)         -> (acc, s)
  in
  let (l,s) = foo [] t in
  (List.rev l, s)


(***** Box operations *********************************************************)

(* 4/10 adding strong param to refsTermsOf, to use different filtering funcs *)
(* TODO might want a separate version for local inf, where maybenulls should be
   considered, and a version for type checking, where they shouldn't *)
(* TODO 8/24: check whether this still avoids extraction. generally clean up *)

let refTermsOf g ?(strong=None) = function
  | TMaybeNull(TQuick(_,QBoxes[URef(l)],_))
  | TQuick(_,QBoxes[URef(l)],_) ->
      (* let _ = Log.log1 "don't call extract [Ref(%s)]\n" (strLoc l) in *)
      [URef l]
  | t ->
      (* let _ = Log.log1 "call extract refTermsOf [%s]\n" (prettyStrTyp t) in *)
      let filter = function
        | URef(l) -> (match strong with
                        | None -> true
                        | Some(b) -> if b then not (isWeakLoc l) else isWeakLoc l)
        | _       -> false in
      TypeTerms.elements (Sub.mustFlow g t ~filter)

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
                     String.concat ", " (List.map strTT l)])

let singleStrongRefTermOf cap g t = singleRefTermOf ~strong:(Some true) cap g t
let singleWeakRefTermOf cap g t   = singleRefTermOf ~strong:(Some false) cap g t

let arrayTermsOf g = function
  | TQuick(_,QBoxes[UArray(t)],_) ->
      (* let _ = Log.log1 "don't call extract [Array(%s)]\n" (strTyp t) in *)
      [UArray t]
  | t ->
      (* Log.log1 "call extract arrayTermsOf [%s]\n" (prettyStrTyp t); *)
      let filter = function UArray _ -> true | _ -> false in
      TypeTerms.elements (Sub.mustFlow g t ~filter)

let arrowTermsOf g t =
  match t with
    | TQuick(_,QBoxes(us),_) ->
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

let joinWorlds v (t1,heap1) (t2,heap2) : prenextyp * heapenv =
  let (l1,s) = joinTypes v t1 t2 in
  let (l2,h) = joinHeapEnvs v heap1 heap2 in
  (mkExists (l1 @ l2) (Typ s), h)

(*
let joinWorlds v w1 w2 =
  let w = joinWorlds v w1 w2 in
  Log.log0 "joinWorlds\n\n";
  Log.log2 "%s\n%s\n\n" (strPrenexTyp (fst w1)) (strHeapEnv (snd w1));
  Log.log2 "%s\n%s\n\n" (strPrenexTyp (fst w2)) (strHeapEnv (snd w2));
  Log.log2 "%s\n%s\n\n" (strPrenexTyp (fst w)) (strHeapEnv (snd w));
  w
*)
  

(***** TC lambda helpers ******************************************************)

let isArrow = function
  | TRefinement(x,PHasTyp(y,UArrow(arr))) when y = wVar x -> Some arr
  | TQuick(_,QBoxes[UArrow(arr)],p) when p = pTru -> Some arr
  | _ -> None

let isArrows t =
  match isArrow t, t with
    | Some(arr), _ -> Some [arr]
    | None, TRefinement(x,PConn("and",ps)) ->
        List.fold_left (fun acc p ->
          match acc, p with
            | Some(l), PHasTyp(y,UArrow(arr)) when y = wVar x -> Some(arr::l)
            | _ -> None
        ) (Some []) ps
    | _, TQuick("v",QBoxes(us),p) when p = pTru ->
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


(***** TS application helpers *************************************************)

type app_rule_result =
  | AppOk   of (prenextyp * heapenv)
  | AppFail of string list

(* for each tuple component of the form xi:ti, add the mapping
     xi |-> wi           if w is a tuple
     xi |-> sel(w,"i")   ow

   INTERESTING 8/29/12: segfault if switch (foo wi acc ti) to (foo wi acc t)
*)
let depTupleSubst t w =
  let rec foo w acc = function
    | TQuick(_,QTuple(l,_),_) ->
        Utils.fold_left_i (fun acc (xio,ti) i ->
          let wi =
            match w with
              | WVal({value=VTuple(vs)})
                when i < List.length vs -> WVal (List.nth vs i)
              | _                       -> sel w (wProj i) in
          match xio with
            | None     -> acc
            | Some(xi) -> let acc = foo wi acc ti in
                          (xi, wi) :: acc) acc l
    | TNonNull(t)
    | TMaybeNull(t) -> foo w acc t
    | _ -> acc
  in
  let subst = foo w [] t in
(*
  Log.log1 "depTupleSubst [%s]\n" (strTyp t);
  List.iter (fun (x,w) -> Log.log2 "ravi %s |-> %s\n" x (strWal w)) subst;
*)
  subst


(* TODO 8/15 
   now with heap envs, can't heapDepTupleSubst select path from
   corresponding values, like depTupleSubst? *)

(*
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

*)

let twoVals cap = function
  | [v1;v2] -> (v1, v2)
  | _       -> err [cap; "wrong number of arguments"]

let threeVals cap = function
  | [v1;v2;v3] -> (v1, v2, v3)
  | _          -> err [cap; "wrong number of arguments"]

let matchQRecd = function
  | TQuick(_,QRecd(recd,b),_) -> Some (recd, b)
  | _                         -> None

let matchQStrLit = function
  | TQuick(k,QBase(BStr),
           PEq(WVal{value=VVar(k')},
               WVal{value=VBase(Str(f))})) when k = k' -> Some f
  | _ -> None

let updQRecd v (recd,b) f t3 =
  let recd' = (f,t3) :: (List.remove_assoc f recd) in
  TQuick ("v", QRecd (recd', b), eq theV (WVal v))


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
        fpr oc_local_inf "  heap formal: %s\n" (strHeap e11);
        fpr oc_local_inf "  inferred heap: %s\n " (strHeap e);
        Some e
      end


(***** Type/loc parameter inference *******************************************)

(** This is tailored to inferring location parameters and type variables for
    object and array primitive operations. Both the Ref and Array type term
    constructors are invariant in their parameter, so the greedy choice
    (e.g. unification) is guaranteed to be good.

    The entry point is

      inferTypLocParams g tVars lVars tIn hIn tActs lActs vAct hAct

 ** Step 1: Find type and value tuples

      Want to collect a tuple vTup of value arguments passed in, and a tuple
      tInTup of type arguments expected, so that we can compare each
      vTup[i] to tInTup[i] to infer missing arguments.
 
 ** Step 2: Inferring location parameters for location formals lVars

      Process lVars in increasing order.

      For each Li:

      - if    there is some tTup[j] = Ref(Li)
        and   G => vTup[j] :: Ref(l)
        then  add Li |-> l to the location substitution

      - if    there is some (L |-> (_:_, Li)) in the heap formal
        and   L |-> l is part of location substitution
        and   (l |-> (_, l')) is in the heap actual
        then  add Li |-> l' to the location substitution

      Notice that for a function that takes a reference to L1, and the
      heap constraint for L1 links to L2, then the location parameter L1
      must appear in lVars before L2. This is how all the primitives
      are written anyway, since it's intuitive.

 ** Step 3: Inferring type parameters for type formals tVars

      For each Ai:

      - if    there is some Lj s.t. (Lj |-> (_:Arr(A), _))
        and   the location substitution maps Lj to l
        and   (l |-> (a, _)) is in the heap actual
        and   G => a :: Arr(T)
        then  add A |-> T to the type substitution

      Note that the first step looks for Arr(A) syntactically, which is
      how all the primitives are written. Might need to make this more
      general later.
*)

let _strTyps ts = String.concat "," (List.map strTyp ts)
let _strVals vs = String.concat "," (List.map strVal vs)

let isValueTuple v = match v.value with
  | VTuple(vs) -> Some vs
  | _          -> None
    (* could also look for v as a tuple dictionary --- that is, a dictionary
       with fields "0" through "n" in order without any duplicates --- but
       no longer need to. see TcDref2.ml for details. *)

(* TODO clean up findActualFromRefValue, findActualFromProtoLink, findArrayActual *)

let findActualFromRefValue g lVar tTup vTup =
  let rec foo i = function
    (* 3/14 added the MaybeNull case since the objects.dref primitives
       now take nullable strong references *)
    | (TQuick(_,QBoxes[URef(LocVar(lVar'))],_) :: ts)
    | (TMaybeNull(TQuick(_,QBoxes[URef(LocVar(lVar'))],_)) :: ts) when lVar = lVar' ->
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
                | HEConcObj(_,lAct) ->
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
    | (LocVar lVar,
       HConcObj (_, TQuick (_, QBoxes [UArray (TQuick (_, QBoxes [UVar x], _))], _), _)) :: cs
      when tVar = x ->
        if not (List.mem_assoc lVar locSubst) then foo cs
        else begin match List.assoc lVar locSubst with
          | None -> foo cs
          | Some(lAct) ->
              if not (List.mem_assoc lAct (snd hAct)) then foo cs
              else begin match List.assoc lAct (snd hAct) with
                | HEConcObj(a,_) ->
                    (match arrayTermsOf g (selfifyVal g a) with
                       | [UArray(t)] -> Some t
                       (* 3/31 Arr({v|v != undef}) and Arr({v'|v' != undef}) *)
                       | UArray(t)::_ -> Some t
                       | _           -> foo cs)
                | HEConc _
                | HEWeakTok _ -> foo cs
              end
        end
    | _ :: cs -> foo cs
    | []      -> None
  in
  foo (snd hForm)

let steps2and3 g tVars lVars tInTup hForm vTup hAct =

  (* Step 2 *)
  let locSubst =
    List.fold_left (fun subst lVar ->
      let maybeActual = 
        match findActualFromRefValue g lVar (List.map snd tInTup) vTup with
          | None       -> findActualFromProtoLink subst lVar hForm hAct
          | Some(lact) -> Some lact in
      ((lVar,maybeActual)::subst)
    ) [] lVars in

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
    match tVars with
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

let inferTypLocParams cap g tVars lVars tIn hIn tActs lActs vAct hAct =
  if List.length tActs <> 0 then None
  else if List.length lActs = List.length lVars then None
  else begin
    fpr oc_local_inf "\n%s\n\n" cap;
    match isValueTuple vAct, tIn with
      | Some(vTup), TQuick("v",QTuple(tInTup,_),_) -> begin
          fpr oc_local_inf "  tInTup: [%s]\n" (_strTyps (List.map snd tInTup));
          fpr oc_local_inf "  vTup:   [%s]\n" (_strVals vTup);
          steps2and3 g tVars lVars tInTup hIn vTup hAct
        end
      | _ -> None
  end


(***** Bidirectional type checking ********************************************)

(***** Initial trivial checks *****)

let checkInconsistent cap =
  Zzz.checkValid (spr "%s false check" cap) pFls

let rec tsVal g h e : typ =
  if !Settings.doFalseChecks && checkInconsistent "tsVal" then tyFls
  else tsVal_ g h e

and tsExp g h e : prenextyp * heapenv =
  if !Settings.doFalseChecks && checkInconsistent "tsExp" then (Typ tyFls, h)
  else tsExp_ g h e

and tcVal g h s e =
  if !Settings.doFalseChecks && checkInconsistent "tcVal" then ()
  else tcVal_ g h s e

and tcExp g h (w: world) e =
  if !Settings.doFalseChecks && checkInconsistent "tcExp" then ()
  else tcExp_ g h w e

(*
and tryTcVal g h s e =
  Zzz.inNewScope (fun () ->
    try (tcVal g h s e; true)
    with Tc_error _ -> false)
*)


(***** Value type synthesis ***************************************************)

and tsVal_ g h = function

  (* 3/15 adding v::Null back in *)
  | {value=VNull} ->
      TQuick ("v", QBoxes [UNull], eq theV wNull)

  | ({value=VBase(bv)} as v) ->
      TQuick ("v", QBase (baseTypOfBaseVal bv), eq theV (WVal v))

  | {value=VVar("__skolem__")} ->
      TQuick ("v", QBase BNum, pTru)

  | {value=VVar(x)} -> selfifyVar g x

  | ({value=VEmpty} as v) ->
      TQuick ("v", QRecd ([], true), eq theV (WVal v))

(*
  | ({value=VExtend(v1,v2,v3)} as v) -> begin
      tcVal g h tyDict v1;
      tcVal g h tyStr v2;
      tcVal g h tyAny v3;
      ty (PEq (theV, WVal v))
    end
*)

  | ({value=VExtend(v1,v2,v3)} as v) -> begin
      let cap =
        spr "TS-Val: %s ++ %s |-> %s" (strVal v1) (strVal v2) (strVal v3) in
      let (t1,t2,t3) = (tsVal g h v1, tsVal g h v2, tsVal g h v3) in
      Sub.types cap g (Typ t1) tyDict;
      Sub.types cap g (Typ t2) tyStr;
      match matchQRecd t1, matchQStrLit t2 with
        | Some(recd,b), Some(f) -> updQRecd v (recd,b) f t3
        | _                     -> ty (eq theV (WVal v))
    end

  | {value=VArray(tInv,vs)} -> begin
      List.iter (tcVal g h tInv) vs;
      let n = List.length vs in
      let ps = (* could add pDict if needed *)
        packed theV :: PEq (arrlen theV, wInt n)
        :: Utils.map_i (fun vi i -> PEq (sel theV (wInt i), WVal vi)) vs in
      TQuick ("v", QBoxes [UArray tInv], pAnd ps)
    end

  | ({value=VTuple(vs)} as v) ->
      let l = List.map (fun v -> (None, tsVal g h v)) vs in
      TQuick ("v", QTuple (l, true), eq theV (WVal v))

  | {value=VFun _} -> failwith "TS-Fun"


(***** Expression type synthesis **********************************************)

and tsExp_ g h = function

  | EVal(v) -> (Typ (tsVal g h v), h)

  | ENewref(l,EVal(v)) ->
      let cap = spr "TS-Newref: %s (%s) in ..." (strLoc l) (strVal v) in
      begin match findCell l h with
        | Some _ -> err ([cap; spr "location [%s] already bound" (strLoc l)])
        | None ->
            let _ = tsVal g h v in
            let h' = (fst h, snd h @ [(l, HEConc v)]) in
            (* probably no need to use the more precise v=VRef(_) *)
            (Typ (tyRef l), h')
      end

  | EDeref(EVal(v)) ->
      let cap = spr "TS-Deref: !(%s)" (strVal v) in
      let t1 = tsVal g h v in
      let l = singleRefTermOf cap g t1 in
      begin match findCell l h with
        | Some(HEConc(v')) -> (Typ (selfifyVal g v'), h)
        | Some(HEConcObj _) -> err ([cap; "can't deref object location"])
        | Some(HEWeakTok _) -> err ([cap; "can't deref weak location"])
        | None -> err ([cap; spr "unbound loc [%s]" (strLoc l)])
      end

  | ESetref(EVal(v1),EVal(v2)) ->
      let cap = spr "TS-Setref: (%s) := (%s)" (strVal v1) (strVal v2) in
      let t = tsVal g h v1 in
      let _ = tsVal g h v2 in
      let l = singleRefTermOf cap g t in
      begin match findAndRemoveCell l h with
        | None -> err ([cap; spr "unbound loc [%s]" (strLoc l)])
        | Some(HEConcObj _, _) -> err ([cap; "can't setref object location"])
        | Some(HEWeakTok _, _) -> err ([cap; "can't setref weak location"])
        | Some(HEConc(v), h0) ->
            let h' = (fst h0, snd h0 @ [(l, HEConc v2)]) in
            (Typ (selfifyVal g v2), h')
      end

  | ENewObj(EVal(v1),l1,EVal(v2),l2) ->
      let cap = spr "TS-NewObj: new (%s, %s, %s, %s)"
        (strVal v1) (strLoc l1) (strVal v2) (strLoc l2) in
      begin match findCell l1 h, findCell l2 h with
        | None, Some(HEConcObj _) ->
            let _ = tcVal g h (tyRef l2) v2 in
            let t1 = tsVal g h v1 in
            let d = freshVar "obj" in
            let h' = (fst h, snd h @ [l1, HEConcObj (vVar d, l2)]) in
            let s = (* probably no need to use the more precise v=VObjRef(_) *)
              TQuick ("v", QBoxes [URef l1], eq (tag theV) (wStr tagObj)) in
            (TExists (d, t1, Typ s), h')
              (* using an existential in case v1 is an array value (really
                 just sugar), which doesn't come equipped with a has-type
                 predicate, but its type t1 does *)
(*
            let _ = tcVal g h tyDict v1 in
            let _ = tcVal g h (tyRef l2) v2 in
            let h' = (fst h, snd h @ [l1, HEConcObj (v1, l2)]) in
            (tyRef l1, h')
*)
        | None, Some _ -> err [cap; spr "loc [%s] isn't a conc obj" (strLoc l2)]
        | None, None -> err [cap; spr "loc [%s] isn't bound" (strLoc l2)]
        | Some _, _ -> err [cap; spr "loc [%s] already bound" (strLoc l1)]
      end

  | EApp(l,EVal(v1),EVal(v2)) ->
      if !Settings.quickTypes then begin
        match tsAppQuick g h (l,v1,v2) with
          | Some(s,h) -> (s, h)
          | None      -> tsAppSlow g h (l,v1,v2)
      end else
        tsAppSlow g h (l,v1,v2)

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

  (* 8/20/12: split TS-Let-Ann into two cases, depending on whether the frame
     annotation is for a function type or not. *)

  | ELet(x,Some(frame),e1,e2) when frameIsNonArrowType frame -> begin
      let gInit = g in
      let ruleName = "TS-Let-Ann-Not-Arrow" in
      let cap = spr "%s: let %s = ..." ruleName x in
      checkBinder cap g x;
      let (s1,h1) = Zzz.inNewScope (fun () -> tsExp g h e1) in
      (* let (s1,h1) = elimSingletonExistentials (s1,h1) in *)
      let tGoal = destructNonArrowTypeFrame frame in
      Sub.types cap g s1 tGoal;
      let (l1,s1) = stripExists s1 in
      let g = tcAddBindings g l1 in
      let g = tcAddBinding g x s1 in
      (* synthesizing x:s1, _not_ the goal tGoal, since need to bring all the
         binders in scope, since they may refered to in h1. so the tGoal
         annotation is simply a check rather than an abstraction. *)
      printBinding (String.make (String.length x) ' ') tGoal ~extraBreak:false;
      maybePrintHeapEnv h1 h;
      let (s2,h2) = tsExp g h1 e2 in
      finishLet cap gInit x (l1 @ [(x,s1)]) (s2,h2)
    end

  | ELet(x,Some(frame),e1,e2) (* when not (frameIsNonArrowType frame) *) -> begin
      let gInit = g in
      let ruleName = "TS-Let-Ann-Arrow" in
      let cap = spr "%s: let %s = ..." ruleName x in
      checkBinder cap g x;
      let (s1,h1) = applyFrame h frame in
      Zzz.inNewScope (fun () -> tcExp g h (s1,h1) e1);
      let (bindings,h1) = heapEnvOfHeap h1 in
      let g = tcAddBindings g bindings in
      let g = tcAddBinding g x s1 in
      maybePrintHeapEnv h1 h;
      let (s2,h2) = tsExp g h1 e2 in
      finishLet cap gInit x [(x,s1)] (s2,h2)
    end

  | ELet(x,None,e1,e2) -> begin
      let gInit = g in
      let ruleName = "TS-Let-Bare" in
      let cap = spr "%s: let %s = ..." ruleName x in
      checkBinder cap g x;
      let (s1,h1) = Zzz.inNewScope (fun () -> tsExp g h e1) in
      (* let (s1,h1) = elimSingletonExistentials (s1,h1) in *)
      let (l1,s1) = stripExists s1 in
      let g = tcAddBindings g l1 in
      let g = tcAddBinding g x s1 in
      maybePrintHeapEnv h1 h;
      let (s2,h2) = tsExp g h1 e2 in
      finishLet cap gInit x (l1 @ [(x,s1)]) (s2,h2)
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
      let g1 = tcAddBinding g x s in
      let (s2,h2) = tsExp g1 h e in
      finishLet (spr "%s: let %s = ..." "TS-Extern" x) g x [(x,s)] (s2,h2)
    end

  | EWeak((m,t,l),e) -> begin
      if isStrongLoc m then err ["TS-EWeak: location should be weak"];
      let g = WeakLoc (m, t, l) :: g in
      Wf.typ "EWeak" g t;
      let h = (fst h, (m, HEWeakTok Frzn) :: snd h) in
      tsExp g h e
    end

  | EAsW(e,w) -> begin
      Wf.world "TS-EAsW:" g w;
      let (tGoal,hGoal) = freshenWorld w in
      tcExp g h (tGoal,hGoal) e;
      let (binders,h) = heapEnvOfHeap hGoal in
      (* TODO use a version of mkExists that adds dummy binders first,
         since binders can mutually refer to each other? *)
      (mkExists binders (Typ tGoal), h)
    end

  | ELabel(x,e) -> failwith "TS-Label: need a goal"

  (* TODO 9/25 revisit *)
  | EBreak(x,EVal(v)) ->
      let cap = spr "TS-Break: break %s (%s)" x (strVal v) in
      let lblBinding =
        try List.find (function Lbl(y,_) -> x = y | _ -> false) g
        with Not_found -> err [cap; "label not found"] in
      begin match lblBinding with
        | Lbl(_,Some(tGoal,hGoal)) -> begin
            tcVal g h tGoal v;
            Zzz.queryRoot := "TS-Break";
            ignore (Sub.heapSat cap g h hGoal);
            (Typ tyFls, h)
          end
        | _ -> err [cap; "no goal for label"]
      end

  | EFreeze(m,ts,EVal(v)) ->
      let cap = spr "ts EFreeze: [%s] [%s] [%s]"
        (strLoc m) (strThawState ts) (strVal v) in
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
                  (Typ (TNonNull (tyRef m)), h')
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
      let cap = spr "ts EThaw: [%s] [%s]" (strLoc l) (strVal v) in
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
                  (TExists (x, tFrzn, Typ t), h')
              | Some(HEWeakTok _, _) -> err [cap; "already thawed"]
              | Some _ -> err [cap; "isn't a weaktok constraint"]
              | None -> err [cap; spr "[%s] location not bound" (strLoc m)]
            end
      end

  | EHeapEnv(l,e) -> begin
      (* TODO could check that all bindings are new and well-formed *)
      if !depth > 0 then err ["TS-HeapEnv: not at top-level"];
      let h1 = (fst h, (snd h) @ l) in
      maybePrintHeapEnv h1 h;
      tsExp g h1 e
    end

  | EThrow(EVal(v)) -> failwith "EThrow"
      (* let _ = tsVal g h v in (tyFls, h) *)

  | ETryCatch _ -> failwith "ETryCatch"

  | ETryFinally _ -> failwith "ETryFinally"

  | ETcFail(s,e) ->
      let fail =
        try let _ = tsExp g h e in false
        with Tc_error _ -> true in
      if fail
        then (Typ tyAny, h)
        else err [spr "TS-Fail: [\"%s\"] should have failed" s]

  | ELoadedSrc(_,e) -> tsExp g h e

  | ELoadSrc(s,_) ->
      failwith (spr "ts ELoadSrc [%s]: should've been expanded" s)

  (* the remaining cases should not make it to type checking, so they indicate
     some failure of parsing or ANFing *)

  | EDict _    -> Anf.badAnf "ts EDict"
  | ETuple _   -> Anf.badAnf "ts ETuple"
  | EArray _   -> Anf.badAnf "ts EArray"
  | EFun _     -> Anf.badAnf "ts EFun"
  | EIf _      -> Anf.badAnf "ts EIf"
  | EApp _     -> Anf.badAnf "ts EApp"
  | ENewref _  -> Anf.badAnf "ts ENewref"
  | EDeref _   -> Anf.badAnf "ts EDeref"
  | ESetref _  -> Anf.badAnf "ts ESetref"
  | ENewObj _  -> Anf.badAnf "ts ENewObj"
  | EBreak _   -> Anf.badAnf "ts EBreak"
  | EThrow _   -> Anf.badAnf "ts EThrow"
  | EFreeze _  -> Anf.badAnf "ts EFreeze"
  | EThaw _    -> Anf.badAnf "ts EThaw"

and tsAppSlow g curHeap ((tActs,lActs,hActs), v1, v2) =

  Zzz.queryRoot := "TS-App";
  let cap = spr "TS-App: [...] (%s) (%s)" (strVal v1) (strVal v2) in
  let t1 = tsVal g curHeap v1 in
  let boxes = arrowTermsOf g t1 in

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

    let t11 = t11 |> substTyp ([],[],[],hSubst) |> expandPreTyp in
    let e11 = e11 |> substHeap ([],[],[],hSubst) |> expandPreHeap in
    Wf.heap "e11 after instantiation"
      (List.fold_left (fun g x -> Var(x,tyAny)::g) g (depTupleBinders t11))
      e11;

    tcVal g curHeap t11 v2;
    let argSubst = (y, WVal v2) :: (depTupleSubst t11 (WVal v2)) in
    let e11 = substHeap (argSubst,[],[],[]) e11 in
    (* TODO heapSubst should collect tuple substitution *)
    let heapSubst = Sub.heapSat cap g curHeap e11 in

    let (t12,e12) = freshenWorld (t12,e12) in

    let polySubst = ([],tSubst,lSubst,hSubst) in
    let (t12,e12) = (substTyp polySubst t12, substHeap polySubst e12) in

    let valueSubst = (argSubst @ heapSubst,[],[],[]) in
    let (t12,e12) = (substTyp valueSubst t12, substHeap valueSubst e12) in
    let (t12,e12) = (expandPreTyp t12, expandPreHeap e12) in
    Wf.heap "e12 after instantiation" g e12;

    let (heapBindings,h) = heapEnvOfHeap e12 in
    let (heapBindings,h) = avoidSingletonExistentials (heapBindings,h) in
    let t = mkExists heapBindings (Typ t12) in
    AppOk (t, h) in (* end tryOne *)

  let result = (* use the first arrow that type checks the call *)
    Utils.fold_left_i (fun acc u i ->
      match acc, u with
        | AppOk _, _ -> acc
        | AppFail(l), UArrow(uarr) -> begin
            (* TODO no need for inNewScope, right? *)
            try tryOne uarr
            with Tc_error(errList) ->
              AppFail (l @ [spr "\n*** box %d: %s" i (strTT u)] @ errList)
          end
        | AppFail(l), _ ->
            AppFail (l @ [spr "box %d isn't an arrow: %s" i (strTT u)])
    ) (AppFail []) boxes in

  match result with
    | AppOk(t,h) -> (t, h)
    | AppFail([]) ->
        let s = spr "0 boxes extracted from type: %s" (strTyp t1) in
        Log.printTcErr [cap; s]
    | AppFail(errors) ->
        let n = List.length boxes in
        let s = spr "%d boxes but none type check the call" n in
        Log.printTcErr (cap :: s :: errors)
        (* the buck stops here, instead of raising Tc_error, since otherwise
           get lots of cascading let-bindings *)


(***** Value type conversion **************************************************)

and tcVal_ g h goal = function

  | {value=VFun(x,e)} -> begin
      let ruleName = "TC-Fun" in
      let g = removeLabels g in
      let checkOne (((ts,ls,hs),y,t1,h1,t2,h2) as arr) =
        checkBinder (spr "%s: formal %s" ruleName y) g y;
        let u = UArrow arr in
        Wf.typeTerm (spr "%s: arrow:\n  %s" ruleName (strTT u)) g u;
        (* let subst = ([(y, wVar x)], [], [], []) in *)
        let vsubst =
          match x with
            | PNode(ps) -> []
            | PLeaf(x) -> [(y, wVar x)] in
        let subst = (vsubst, [], [], []) in
        let t2 = substTyp subst t2 in
        let h2 = substHeap subst h2 in
        let g = List.fold_left (fun acc x -> TVar(x)::acc) g ts in
        let g = List.fold_left (fun acc x -> LVar(x)::acc) g ls in
        let g = List.fold_left (fun acc x -> HVar(x)::acc) g hs in
        Zzz.inNewScope (fun () ->
          (* since input heap can refer to arg binders, need to process t1 first *)
          let g = tcAddBindingPat g x t1 in
          let (bindings,h) = heapEnvOfHeap h1 in
          let g = tcAddBindings g bindings in
          tcExp g h (t2,h2) e;
        )
      in
      match isArrows goal with 
        | Some(l) -> List.iter checkOne l
        | None    -> err [spr "%s: goal should be one or more arrows\n  %s"
                            ruleName (strTyp goal)]
    end

  | v ->
      let s = tsVal g h v in
      let _ = Zzz.queryRoot := "TC-EVal" in
      Sub.types (spr "TC-EVal: %s" (strVal v)) g (Typ s) goal


(***** Expression type conversion *********************************************)

and tcExp_ g h goal = function

  | EVal(v) -> begin
      let (sGoal,hGoal) = goal in
      tcVal g h sGoal v;
      Zzz.queryRoot := "TC-EVal";
      ignore (Sub.heapSat (spr "TC-Val: %s" (strVal v)) g h hGoal)
    end

  | ENewref(l,EVal(v)) ->
      let cap = spr "TC-Newref: ref (%s, %s)" (strLoc l) (strVal v) in
      let w = tsExp g h (ENewref(l,EVal(v))) in
      let _ = Zzz.queryRoot := "TC-Newref" in
      ignore (Sub.worldSat cap g w goal)

  | EDeref(EVal(v)) ->
      let w = tsExp g h (EDeref(EVal(v))) in
      let cap = spr "TC-Deref: !(%s)" (strVal v) in
      let _ = Zzz.queryRoot := "TC-Deref" in
      ignore (Sub.worldSat cap g w goal)

  | ESetref(EVal(v1),EVal(v2)) ->
      let cap = spr "TC-Setref: (%s) := (%s)" (strVal v1) (strVal v2) in
      let w = tsExp g h (ESetref(EVal(v1),EVal(v2))) in
      let _ = Zzz.queryRoot := "TC-Setref" in
      ignore (Sub.worldSat cap g w goal)

  | ENewObj(EVal(v1),l1,EVal(v2),l2) ->
      let cap = spr "TC-NewObj: new (%s, %s, %s, %s)"
        (strVal v1) (strLoc l1) (strVal v2) (strLoc l2) in
      let w = tsExp g h (ENewObj(EVal(v1),l1,EVal(v2),l2)) in
      let _ = Zzz.queryRoot := "TC-NewObj" in
      ignore (Sub.worldSat cap g w goal)

  | EApp(l,EVal(v1),EVal(v2)) ->
      let cap = spr "TC-App: [...] (%s) (%s)" (strVal v1) (strVal v2) in
      let w = tsExp g h (EApp(l,EVal(v1),EVal(v2))) in
      let _ = Zzz.queryRoot := "TC-App" in
      ignore (Sub.worldSat cap g w goal)

  (***** all typing rules that use special let-bindings should be above *****)

  | ELet(x,None,e1,e2) ->
      (* let cap = spr "TC-Let-Bare: let %s = ..." x in *)
      ignore (tsExp g h (ELet (x, None, e1, EAsW (e2, goal))))

  | ELet(x,Some(a1),e1,e2) ->
      (* let cap = spr "TC-Let-Ann: let %s = ..." x in *)
      ignore (tsExp g h (ELet (x, Some a1, e1, EAsW (e2, goal))))

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

  | EAsW(e,w) -> begin
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

  | EHeapEnv(l,e) -> failwith "tc EHeapEnv"

  | ELoadedSrc _ -> failwith "tc ELoadedSrc"
  | ELoadSrc(s,_) ->
      failwith (spr "tc ELoadSrc [%s]: should've been expanded" s)

  | EThrow _ -> failwith "tc EThrow"
  | ETryCatch _ -> failwith "tc ETryCatch"
  | ETryFinally _ -> failwith "tc ETryFinally"

  | ETcFail(s,e) ->
      let fail =
        try let _ = tcExp g h goal e in false
        with Tc_error _ -> true in
      if fail
        then ()
        else err [spr "TC-Fail: [\"%s\"] should have failed" s]

  (* the remaining cases should not make it to type checking, so they indicate
     some failure of parsing or ANFing *)

  | EDict _    -> Anf.badAnf "tc EDict"
  | ETuple _   -> Anf.badAnf "tc ETuple"
  | EArray _   -> Anf.badAnf "tc EArray"
  | EFun _     -> Anf.badAnf "tc EFun"
  | EIf _      -> Anf.badAnf "tc EIf"
  | EApp _     -> Anf.badAnf "tc EApp"
  | ENewref _  -> Anf.badAnf "tc ENewref"
  | EDeref _   -> Anf.badAnf "tc EDeref"
  | ESetref _  -> Anf.badAnf "tc ESetref"
  | ENewObj _  -> Anf.badAnf "tc ENewObj"
  | EBreak _   -> Anf.badAnf "tc EBreak"


(***** TS-App optimized rules *************************************************)

(* these should derive types consistent with the primitive signatures *)

and tsAppQuick g h (poly,vFun,vArg) = match (poly,vFun,vArg) with

  | ([],[],[]), {value=VVar("get")}, {value=VTuple(vs)} ->
      let cap = spr "TS-App-Get: get (%s)" (strVal vArg) in
      let (v1,v2) = twoVals cap vs in
      let (t1,t2) = (tsVal g h v1, tsVal g h v2) in
      begin match matchQRecd t1, matchQStrLit t2 with
        | Some(recd,exactDom), Some(f) ->
            if List.mem_assoc f recd then Some (Typ (List.assoc f recd), h)
            else if exactDom then err [cap; spr "missing field \"%s\"" f]
            else None
        | _ ->
            None
      end

  | ([],[],[]), {value=VVar("set")}, {value=VTuple(vs)} ->
      let cap = spr "TS-App-Set: set (%s)" (strVal vArg) in
      let (v1,v2,v3) = threeVals cap vs in
      Some (Typ (tsVal g h (wrapVal pos0 (VExtend(v1,v2,v3)))), h)

  | ([],[],[]), {value=VVar("getPropObj")}, {value=VTuple(vs)} -> begin
      let cap = spr "TS-App-GetPropObj: getPropObj (%s)" (strVal vArg) in
      let (v1,v2) = twoVals cap vs in
      let (t1,t2) = (tsVal g h v1, tsVal g h v2) in
      let l1 = singleRefTermOf cap g t1 in
      match findCell l1 h with
        | Some(HEConcObj(d1,l2)) ->
            (match matchQRecd (tsVal g h d1), matchQStrLit t2 with
               | Some(recd,exactDom), Some(f) ->
                   (match getPropObj g h recd exactDom f l2 with
                      | Some(s) -> Some (Typ s, h)
                      | None    -> None)
               | _ -> None)
        | _ -> err [cap; spr "%s not an object in heap" (strLoc l1)]
    end

  | ([],[],[]), {value=VVar("setPropObj")}, {value=VTuple(vs)} -> begin
      let cap = spr "TS-App-SetPropObj: setPropObj (%s)" (strVal vArg) in
      if List.length vs <> 3 then err [cap; "wrong number of arguments"];
      let (v1,v2,v3) = threeVals cap vs in
      let (t1,t2) = (tsVal g h v1, tsVal g h v2) in
      let l1 = singleRefTermOf cap g t1 in
      match findAndRemoveCell l1 h with
        | Some(HEConcObj(d1,l2),h0) ->
            (match matchQRecd (tsVal g h d1), matchQStrLit t2 with
               | Some(recd,exactDom), Some(f) ->
                   let t3 = tsVal g h v3 in
                   let d = freshVar "setobj" in
                   let vUpd = wrapVal pos0 (VExtend(d1,v2,v3)) in
                   let s = updQRecd vUpd (recd,exactDom) f t3 in
                   let s = addPredicate (pNot (eq (WVal v1) wNull)) s in
                   let h' = (fst h0, snd h0 @ [(l1, HEConcObj (vVar d, l2))]) in
                   Some (TExists (d, s, Typ (selfifyVal g v3)), h')
               | _ -> None)
        | _ -> err [cap; spr "%s not an object in heap" (strLoc l1)]
    end

  | ([],[],[]), {value=VVar("getPropArr")}, {value=VTuple(vs)} -> begin
      let cap = spr "TS-App-GetPropArr: getPropArr (%s)" (strVal vArg) in
      let (v1,v2) = twoVals cap vs in
      let (t1,t2) = (tsVal g h v1, tsVal g h v2) in
      let l1 = singleRefTermOf cap g t1 in
      match findCell l1 h with
        | Some(HEConcObj(a,l2)) ->
            (match tsVal g h a, matchQStrLit t2 with
               (* resolve "length" directly *)
               | TQuick(_,QBoxes[UArray(_)],_), Some("length") ->
                   let p =
                     pAnd [pNot (eq (WVal v1) wNull);
                           pImp (packed (WVal a))
                                (eq theV (arrlen (WVal a)))]
                   in
                   Some (Typ (TQuick ("v", QBase BInt, p)), h)
               (* resolve all other keys from prototype chain *)
               | TQuick(_,QBoxes[UArray(_)],_), Some(f) ->
                   (match getPropObj g h [] true f l2 with
                      | Some(s) -> Some (Typ s, h)
                      | None    -> None)
               | _ -> None)
        | _ -> err [cap; spr "%s not an object in heap" (strLoc l1)]
    end

  | ([],[],[]), {value=VVar("getProp")}, {value=VTuple(vs)} ->
      tsAppQuickTry g h ["getPropObj"; "getPropArr"] vArg

  | ([],[],[]), {value=VVar("getElem")}, {value=VTuple(vs)} ->
      tsAppQuickTry g h ["getPropObj"; "getIdx"; "getPropArr"] vArg

  | ([],[],[]), {value=VVar("setProp")}, {value=VTuple(vs)} ->
      tsAppQuickTry g h ["setPropObj"; "setPropArr"] vArg

  | ([],[],[]), {value=VVar("setElem")}, {value=VTuple(vs)} ->
      tsAppQuickTry g h ["setPropObj"; "setIdx"; "setPropArr"] vArg

  | _ -> None

and getPropObj g h recd exactDom f lPro =
  if List.mem_assoc f recd then Some (List.assoc f recd)
  else if not exactDom then None
  else if lPro = lRoot then Some tyUndef
  else begin
    match findCell lPro h with
      | Some(HEConcObj(d2,lProPro)) ->
          (match matchQRecd (tsVal g h d2) with
             | Some(recd2,exactDom2) -> getPropObj g h recd2 exactDom2 f lProPro
             | None -> None)
      | Some _ -> failwith "getPropObj: bad constraint"
      | None -> failwith "getPropObj: could return HeapSel here"
  end

and tsAppQuickTry g h fs vArg =
  match fs with
    | []   -> None
    | f::l -> (match tsAppQuick g h (([],[],[]), vVar f, vArg) with
                 | Some(s,h) -> Some (s, h)
                 | None      -> tsAppQuickTry g h l vArg)


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
         foo (tcAddBinding acc sk tyNum) (i+1)
  in
  foo g 1

let initialEnvs () =
  let h_init = "H_ROOT" (* "H_emp" *) in
  let g = [HVar h_init] in
  let g = tcAddBinding g "v" tyAny in
  let g = addSkolems g in
  let h = ([h_init], [lRoot, HEConcObj (vNull, lRoot)]) in
  let _ = maybePrintHeapEnv h ([],[]) in
  (g, h)

let typecheck e =
  let oc_num_q = open_out (Settings.out_dir ^ "num-queries.txt") in
  assertIntegerness e;
  let (g,h) = initialEnvs () in
  try begin
    ignore (tsExp g h e);
    Sub.writeStats ();
    Zzz.writeQueryStats ();
    let s = spr "OK! %d queries." !Zzz.queryCount in
    fpr oc_num_q "%d" !Zzz.queryCount;
    Log.log1 "\n%s\n" (Utils.greenString s);
    if not !Log.printToStdout then Printf.printf "\n%s\n" (Utils.greenString s);
  end with Tc_error(s) ->
    Log.printTcErr s

let typecheck e =
  BNstats.time "Tc.typecheck" typecheck e
