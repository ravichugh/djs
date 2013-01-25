
open Lang
open LangUtils


(***** Collecting type terms, or "boxes" **************************************)

(* TODO so that all boxes are readily available and no need to re-compute:
   - rig registerBox to add/remove boxes along with logical scope.
   - maintain boxes incrementally in sync with type env.
*)

let typeTerms_ g =
  let boxes = [UNull] in
  let pastPrelude = ref false in

  (* iterate over bindings in the order in which they appear in the
     program. by default, excluding the boxes from objects.dref since type
     checking will syntactically track those arrows. use the -tryAllBoxes
     flag to force them to be included. _not_ excluding the boxes from
     js_natives.dref since the functions in Object.prototype and
     Array.prototype may be inherited. boxes from more recent bindings
     appear earlier in the output list, so the arrows from js_natives
     will be at the end. *)

  let g = List.rev g in
  if !Settings.tryAllBoxesHack then pastPrelude := true;
  List.fold_left (fun acc -> function
    | Var(x,t) when !pastPrelude   -> foldTyp ~fTT:Utils.maybeAddToList acc t
    | Var("end_of_dref_objects",_) -> (pastPrelude := true; acc)
    | _                            -> acc) boxes g

let typeTerms_ g =
  Stats.time "Sub.typeTerms_" (fun () -> typeTerms_ g)


(***** Type extraction, or "unboxing" *****************************************)

let oc_extract = open_out (Settings.out_dir ^ "extract.txt")
let logExtract ?(nl=true) s =
  fpr oc_extract "%s%s" s (if nl then "\n" else "");
  flush oc_extract

let mustFlowIterator_ usedBoxes ?(filter = fun _ -> true) g t =
  let boxes =
    Utils.subtractList (typeTerms_ g) usedBoxes
    |> List.append [UNull]
    |> List.filter filter
    |> ref
  in
  logExtract (spr "%s" (String.make 80 '-'));
  logExtract (spr "Extract boxes from %s\n" (strTyp t));
  let rec next () =
    match !boxes with
      | [] -> None
      | u::rest ->
          let _ = boxes := rest in
          let maybeBox =
            Zzz.inNewScope (fun () ->
              let x = freshVarX "extract" in
              Zzz.addBinding x t;
              Zzz.doingExtract := true;
              logExtract ~nl:false (spr "  %s ... " (strTT u));
              let b = Zzz.checkValid "mustFlow" (hastyp (wVar x) u) in
              logExtract (spr "%s\n" (if b then "yes" else "no"));
              Zzz.doingExtract := false;
              if b then Some u else None)
          in
          (match maybeBox with
            | Some(u) -> Some u
            | None    -> next ())
  in
  next


(***** Heap Manipulation ******************************************************)

(*

(* TODO for now, copied and simplified from TcDref *)

let simpleTcAddBinding ?isNew:(isNew=true) x s g =
  Zzz.addBinding ~isNew x (applyTyp s (wVar x));
  let g' = Var(x,s)::g in
  g'

let simpleTcRemoveBinding () =
  Zzz.removeBinding ();
  ()

let simpleTcRemoveBindingN n =
  for i = 1 to n do simpleTcRemoveBinding () done


(* TODO can't directly use the version in TcDref, since that one uses
   tcAddBinding, which uses tryDestruct, which uses Sub.extraction *)

let simpleSnapshot cap g h =
  let l = List.map snd (snd h) in
  if l <> [] then Zzz.dump (spr "; snapshot added some bindings [%s]" cap);
  let (n,g1) = 
    List.fold_left (fun (k,acc) -> function
      | HConc(None,_) | HConcObj(None,_,_) -> failwith "simpleSnapshot"
      | HConc(Some(x),_) | HConcObj(Some(x),_,_) -> (k+1, simpleTcAddBinding x tyAny acc)
      | HWeakTok _ -> (k, acc)
    ) (0,g) l
  in
  let g2 = 
    List.fold_left (fun acc -> function
      | HConc(None,_) | HConcObj(None,_,_) -> failwith "simpleSnapshot"
      | HConc(Some(x),s) | HConcObj(Some(x),s,_) -> simpleTcAddBinding ~isNew:false x s acc
      | HWeakTok _ -> acc
    ) g1 l
  in
  (n, g2)

*)


(***** Helpers ****************************************************************)

let rec findLocInHeapEnv l = function
  | (l',hc)::rest -> if l = l' then Some hc else findLocInHeapEnv l rest
  | []            -> None

let die_ errList finalMsgs = err (errList @ finalMsgs)
let die  errList finalMsg  = err (errList @ [finalMsg])

let checkLength s errList l1 l2 =
  if List.length l1 <> List.length l2
  then die errList (spr "different number of %s args" s)
  else ()

let maybeStrHeapEnvCell cs l =
  if List.mem_assoc l cs
  then let hc = List.assoc l cs in strHeapEnvCell hc
  else "MISSING"

let strHeapSat (hs1,cs1) (hs2,cs2) =
  String.concat "\n"
    [ spr "  %s |= %s" (String.concat "++" hs1) (String.concat "++" hs2)
    ; String.concat "\n"
        (List.map (fun (l,hc) ->
           spr "  %s |-> %s |= %s"
             (strLoc l) (maybeStrHeapEnvCell cs1 l) (strHeapCell hc)) cs2)
    ; String.concat "\n"
        (List.filter ((<>) "")
           (List.map (fun (l,hc) ->
              if List.mem_assoc l cs2 then ""
              else spr "  %s |-> %s |= MISSING"
                     (strLoc l) (strHeapEnvCell hc)) cs1))
    ]
  
(*

(* TODO move this helper into checkHeaps and/or factor common parts with
   checkHeapSat *)

type obligation =
  | OConc of loc * vvar * typ
  | OWeak of loc * typ * typ

let heapSubstAndObligations errList cs1 cs2 =
  let foo (acc1,acc2) (l,hc2) =
    try begin
      let hc1 = snd (List.find (fun (l',_) -> l = l') cs1) in
      match hc1, hc2 with
        | HConc(None,_), HConc(None,_)
        | HConcObj(None,_,_), HConcObj(None,_,_) ->
            failwith "heapSubstAndObligations"
        | HConc(Some(y1),_), HConc(Some(y2),s2) ->
            ((y2, wVar y1) :: acc1, OConc (l, y2, s2) :: acc2)
        | HConcObj(Some(y1),_,l1'), HConcObj(Some(y2),s2,l2') ->
            if l1' = l2' then
              ((y2, wVar y1) :: acc1, OConc (l, y2, s2) :: acc2)
            else
              die_ errList
                [spr "proto links for [%s] differ:" (strLoc l);
                 spr "  %s" (strLoc l1');
                 spr "  %s" (strLoc l2')]
        | HWeakTok(x), HWeakTok(y) ->
            if x = y then (acc1, acc2)
            else die errList (spr
                   "thaw states for [%s] differ: [%s] [%s] "
                   (strLoc l) (strThawState x) (strThawState y))
        | _ ->
            die errList (spr
              "constraints for [%s] have different shape" (strLoc l))
    end with Not_found ->
      die errList (spr "no location constraint for [%s]" (strLoc l))
  in
  List.fold_left foo ([],[]) cs2

(* 3/31: only check the shallow constraints in the input heap, since
   after substituting the heap actual, there will be a bunch of
   identical locations to check *)
let filterObligations obligations = function
  | None -> obligations
  | Some(locs) ->
      List.filter
        (function OConc(l,_,_) | OWeak(l,_,_) -> List.mem l locs)
        obligations

*)

(* allow a function type to be weakened by adding additional bindings for
   locations l that are not needed by the arrow:

     S1 / E1 -> S2 / E2   <:   S1 / E1 + (l |-> T) -> S2 / E2 + (l |-> T)

     S1 / E1 -> S2 / E2   <:   S1 / E1 + (m |-> frzn) -> S2 / E2 + (m |-> frzn)
*)
let weakenArrowHeaps (cs11,cs12) (cs21,cs22) =
  let toAdd =
    List.fold_left (fun acc (l,hc) ->
      if not (List.mem_assoc l cs22) then acc
      else if List.mem_assoc l cs11  then acc
      else if List.mem_assoc l cs12  then acc
      else begin match hc with
        | HStrong(None,t,lo,ci) ->
            begin match List.assoc l cs22 with
              | HStrong(None,t',lo',_) when t = t' && lo = lo' ->
                  (l, HStrong (None, t, lo, ci)) :: acc
              | _ -> acc
            end
        | HWeak(Frzn) -> (l, HWeak Frzn) :: acc
        | _ -> acc
      end
    ) [] cs21
  in
  (cs11 @ toAdd, cs12 @ toAdd)

(* allowing natives to be dropped from the arrows on the _left_,
   since natives should never be tampered with.
   TODO should check that the function does not modify them. *)
let dropNatives cs =
  List.rev (List.fold_left (fun acc (l,hc) ->
    if List.mem_assoc l frozenNatives then acc
    else if !Settings.bxMode && List.mem_assoc l frozenBxNatives then acc
    else (l,hc) :: acc
  ) [] cs)

(* TODO until existential locations and cleaning locals is added, allowing
   &x |-> T to be dropped from the _left_ arrow if it is unmodified and
   does not appear at all in the right arrow. *)
let tempDropExistentialLocs (cs11,cs12) (cs21,cs22) =
  let (cs11,cs12) =
    List.fold_left (fun (cs11AddThings,cs12RemoveThings) (l,hc) ->
      match l with
        | LocConst(x) when Utils.strPrefix x "&" ->
            if List.mem_assoc l cs12
               && hc = List.assoc l cs12
               && not (List.mem_assoc l cs21)
               && not (List.mem_assoc l cs22)
            then (cs11AddThings, List.remove_assoc l cs12RemoveThings)
            else ((l,hc) :: cs11AddThings, cs12RemoveThings)
        | _ -> ((l,hc) :: cs11AddThings, cs12RemoveThings)
    ) ([], cs12) cs11
  in
  (List.rev cs11, List.rev cs12)

let isDummyBinder x = (* to match LangParser *)
  Utils.strPrefix x "_underscore"

let simpleCheckArrows
      ((ts1,ls1,hs1),x1,t11,(hs11,cs11),t12,(hs12,cs12))
      ((ts2,ls2,hs2),x2,t21,(hs21,cs21),t22,(hs22,cs22)) =

  let (cs11,cs12) = (dropNatives cs11, dropNatives cs12) in
  let (cs21,cs22) = (dropNatives cs21, dropNatives cs22) in

  let (cs11,cs12) = weakenArrowHeaps (cs11,cs12) (cs21,cs22) in

  let (cs11,cs12) = tempDropExistentialLocs (cs11,cs12) (cs21,cs22) in

  (x1 = x2 || (isDummyBinder x1 && isDummyBinder x2))
  && (ts1,ls1,hs1,t11,t12) = (ts2,ls2,hs2,t21,t22)
  && (hs11, hs21) = (hs21, hs22)
  && ((cs11 = cs21) || (List.sort compare cs11 = List.sort compare cs21))
  && ((cs12 = cs22) || (List.sort compare cs12 = List.sort compare cs22))

(* idea for the hack*Binders functions is to optimistically replace the binders
   of the RHS arrow with those from the LHS arrow. if the binders of the RHS
   appear in refinements, then z3 should complain that there are undefined
   symbols. TODO need to redo this, of course. *)

let hackTypeBinders t1 t2 =
  match t1, t2 with
    | TRefinement(x,_), TRefinement(_,p) -> TRefinement (x, p)
    | TQuick(x,_,_), TQuick(_,qt,p) -> TQuick (x, qt, p)
    | _ -> t2 (* failwith (spr "hackType\n%s\n%s\n" (strTyp t1) (strTyp t2)) *)

let hackHeapBinders cs1 cs2 =
  List.map (fun (l,hc2) ->
    if not (List.mem_assoc l cs1) then (l, hc2)
    else
      match List.assoc l cs1, hc2 with
        | HStrong(Some(x),_,_,_), HStrong(Some(_),t,lo,ci) ->
            (l, HStrong (Some x, t, lo, ci)) 
        | _ ->
            (l, hc2)
  ) cs2

let hackBinders arr1 arr2 =
  let (_,x1,t11,(_,cs11),t12,(_,cs12)) = arr1 in
  let (l2,_,t21,(hs21,cs21),t22,(hs22,cs22)) = arr2 in
  let arr =
    (l2, x1,
     hackTypeBinders t11 t21, (hs21, hackHeapBinders cs11 cs21),
     hackTypeBinders t12 t22, (hs22, hackHeapBinders cs12 cs22))
  in
  arr


(***** Subtyping **************************************************************)

let oc_quick = open_out (Settings.out_dir ^ "quick-types.txt")
let (count_quick,count_slow) = (ref 0, ref 0)

let tallyQuick s1 s2 =
  fpr oc_quick "Discharged quick:\n  %s\n  %s\n\n" s1 s2; incr count_quick

let tallySlow s1 s2 =
  fpr oc_quick "Discharged slow:\n  %s\n  %s\n\n" s1 s2; incr count_slow

let rec bindExistentials g = function
  | Typ(s) -> (g, s)
  | TExists(x,s1,s2) ->
      (Zzz.addBinding x s1; bindExistentials (Var(x,s1)::g) s2)

let rec checkTypes errList usedBoxes g t1 t2 =
  let (s1,s2) = (strPrenexTyp t1, strTyp t2) in
  let errList =
    errList @ [spr "Sub.checkTypes:\n   t1 = %s\n   t2 = %s" s1 s2] in
  Zzz.inNewScope (fun () ->
    let (g,t1) = bindExistentials g t1 in
    if !Settings.quickTypes && quickCheckTypes errList usedBoxes g (t1,t2)
    then tallyQuick s1 s2
    else let v = freshVar "v" in
         let _ = Zzz.addBinding v t1 in
         let _ = checkFormula errList usedBoxes g (applyTyp t2 (wVar v)) in
         tallySlow s1 s2)

  (* binding existentials even for quickCheckTypes, since it may recursively
     call checkTypes for sub-obligations. *)

and quickCheckTypes errList usedBoxes g = function
  | _, t when t = tyAny -> true
  | TQuick(_,QBase(BInt),_), TQuick(_,QBase(BNum),p) -> p = pTru
  | TQuick(_,QBase(bt),_), TQuick(_,QBase(bt'),p) -> bt = bt' && p = pTru
  | TQuick(_,QBase(BInt),_), TBaseUnion(l) when List.mem BNum l -> true
  | TQuick(_,QBase(bt),_), TBaseUnion(l) -> List.mem bt l
  | TQuick(_,QRecd(l1,_),_), TQuick(_,QRecd(l2,_),p) when p = pTru -> begin
      List.iter (fun (f,t2) ->
        if List.mem_assoc f l1
        then checkTypes errList usedBoxes g (Typ (List.assoc f l1)) t2
        else die errList (spr "Missing field \"%s\"." f)
      ) l2;
      true
    end
  | TQuick(_,QTuple(l1,_),_), TQuick(_,QTuple(l2,_),p) when p = pTru ->
      if isDepTuple l2 then false
      else if List.length l1 < List.length l2 then false
      else begin
        List.iter
          (function (t1,t2) -> checkTypes errList usedBoxes g (Typ t1) t2)
          (List.combine
             (List.map snd (Utils.take (List.length l2) l1))
             (List.map snd l2));
        true
      end
  | TQuick(_,QBoxes(l1),_), TQuick(_,QBoxes(l2),p) when p = pTru ->
      List.for_all (fun u -> List.mem u l1) l2
  | TQuick(_,QBoxes(us),_), TMaybeNullRef(l,_) when List.mem (URef l) us ->
      true
  | TNonNullRef(l), TQuick(_,QBoxes[URef(l')],p) when p = pTru && l = l' ->
      true
  | TQuick(_,QBase(bt),_), t when t = tyNotUndef && bt <> BUndef ->
      true
  | _ ->
      false

and checkFormula errList usedBoxes g p =
  let clauses = Cnf.convert p in
  let n = List.length clauses in
  Utils.iter_i
    (fun (pi,qi) i ->
       Zzz.inNewScope (fun () ->
         Zzz.assertFormula pi;
         let (s1,s2) = (strForm pi, strForm (Cnf.orHasTyps qi)) in
         let errList =
           errList @ [spr "Clause %d/%d:\n   %s\n~> %s" (i+1) n s1 s2] in
         checkUnPreds errList usedBoxes g qi))
    clauses

and checkUnPreds errList usedBoxes g qs =
  if Zzz.checkValid "I-Valid" (Cnf.orHasTyps qs) then ()
  else if List.exists (checkHasTyp errList usedBoxes g) qs then ()
  else die errList "Cannot discharge this clause."

and checkHasTyp errList usedBoxes g (w,u) =
  let iterator = mustFlowIterator_ usedBoxes g (ty (eq theV w)) in
  let rec tryOne () =
    match iterator () with
      | None     -> false
      | Some(u') -> if checkTypeTerms errList usedBoxes g u' u
                    then true
                    else tryOne ()
  in
  tryOne ()

and checkTypeTerms errList usedBoxes g u1 u2 =
  if u1 = u2 then true else
  let errList =
    errList @ [spr "checkTypeTerms:\n\n   %s\n\n<: %s" (strTT u1) (strTT u2)] in
  match u1, u2 with
    | UVar(x), UVar(y) -> x = y
    | URef(x), URef(y) -> x = y
    | UNull, URef(y)   -> isWeakLoc y
    | UArrow(arr1), UArrow(arr2) -> checkArrows errList usedBoxes g arr1 arr2
    | UArray(t1), UArray(t2) -> begin
        (* t1 = t2 (* add bivariance back in if needed *) *)
        try (* ideally want a version that returns bool instead of failing *)
          let _ = checkTypes errList usedBoxes g (Typ t1) t2 in
          let _ = checkTypes errList usedBoxes g (Typ t2) t1 in
          true
        with Tc_error _ ->
          false
      end
    | _ -> die errList "Syntactic types don't match up."


and checkArrows errList usedBoxes g
      (((ts1,ls1,hs1),x1,t11,e11,t12,e12) as arr1)
      (((ts2,ls2,hs2),x2,t21,e21,t22,e22) as arr2) =

  (* TODO keep stats about checkArrow *)

  if simpleCheckArrows arr1 arr2 then true
  else if simpleCheckArrows arr1 (hackBinders arr1 arr2) then true
  else die errList "need to restore Sub.checkArrows"

(*
(* TODO 3/10
  checkLength "type" errList ts1 ts2;
  checkLength "loc" errList ls1 ls2;
  checkLength "heap" errList hs1 hs2;
*)
  if List.length ts1 <> List.length ts2
     || List.length ls1 <> List.length ls2
     || List.length hs1 <> List.length hs2 then false
  else
  

  let (tSubst,lSubst,hSubst) =
    (List.combine ts1 (List.map (fun x -> ty (PUn(HasTyp(theV,UVar(x))))) ts2),
     List.combine ls1 (List.map (fun x -> LocVar x) ls2),
     List.combine hs1 (List.map (fun x -> ([x],[])) hs2)) in

  let subst = ([], tSubst, lSubst, hSubst) in
  let t11 = substTyp subst t11 in
  let e11 = substHeap subst e11 in

  (* TODO redo this, since not using worlds *)

  let errList' =
    errList @ [spr "input worlds:\n   %s\n / %s\n < %s\n / %s"
                 (prettyStrTyp t21) (prettyStrHeap e21)
                 (prettyStrTyp t11) (prettyStrHeap e11)]
  in
  let vSubst = checkWorlds errList' usedBoxes g (t21,e21) (t11,e11) in
  let vSubst = (x1, wVar x2)::vSubst in

  let subst = (vSubst, tSubst, lSubst, hSubst) in
  let t12 = substTyp subst t12 in
  let e12 = substHeap subst e12 in

  let errList' =
    errList @ [spr "output worlds:\n   %s\n / %s\n < %s\n / %s"
                 (prettyStrTyp t12) (prettyStrHeap e12)
                 (prettyStrTyp t22) (prettyStrHeap e22)]
  in
  Zzz.pushScope ();
  let (n,g) = simpleSnapshot "sub-arrow" g e21 in
  Zzz.pushBinding x2 (applyTyp t21 (wVar x2));
  ignore (checkWorlds errList' usedBoxes g (t12,e12) (t22,e22));
  Zzz.popBinding ();
  simpleTcRemoveBindingN n;
  Zzz.popScope ();

  true
*)

(*
and checkHeaps errList ?(locsOpt=None) usedBoxes g h1 h2 =
  let errList =
    errList @ [spr "checkHeaps:\n  %s\n< %s"
                 (prettyStrHeap h1) (prettyStrHeap h2)] in
(*
  if h1 = botHeap then botSubst
  else if h1 = h2 then []
*)
  if h1 = h2 then []
  else begin

    (* check heap variables *)
    let ((hs1,cs1),(hs2,cs2)) = (h1, h2) in
    let (hs1,hs2) = (List.sort compare hs1, List.sort compare hs2) in
    if hs1 <> hs2 then
      die errList (spr
        "heap variables not the same:\n   %s\n!= %s"
        (String.concat "," hs1) (String.concat "," hs2));

    (* check location constraints *)
    let (binderSubst,obligations) = heapSubstAndObligations errList cs1 cs2 in
    let obligations = filterObligations obligations locsOpt in (* 3/31 *)
    Zzz.pushScope ();
    let (n,g) = simpleSnapshot "check-heaps" g h1 in
    ignore (List.fold_left (fun errList -> function
      | OConc(l,x2,s2) ->
          let p = applyTyp s2 (wVar x2) in
          let p = substForm (binderSubst,[],[],[]) p in
          let errList' =
            errList @ [spr "Checking location [%s] ..." (strLoc l)] in
          let _ = checkFormula errList' usedBoxes g p in
          errList @ [spr "Checked location [%s]" (strLoc l)]
      | OWeak(l,t1,t2) ->
          let _ = failwith "shouldn't be any OWeak" in
          (* TODO 3/14 issue with theV inside UArray typ_term... right now,
             not checking OWeak obligations, since the typing rules don't
             have a way of changing them anyway...
          let _ = checkTypes errList usedBoxes g t1 t2 in
          checkTypes errList usedBoxes g t2 t1
          *)
          errList
    ) errList obligations);
    simpleTcRemoveBindingN n;
    Zzz.popScope ();
    binderSubst
  end
*)

(*
and checkWorlds errList usedBoxes g (t1,h1) (t2,h2) =
  let errList = errList @ ["checkWorlds:"] in
  let subst = checkHeaps errList usedBoxes g h1 h2 in
  Zzz.pushScope ();
  let (n,g) = simpleSnapshot "check-worlds" g h1 in
  checkTypes errList usedBoxes g t1 (substTyp (subst,[],[],[]) t2);
  simpleTcRemoveBindingN n;
  Zzz.popScope ();
  subst
*)

(* 8/14 adding checkHeapSat and checkWorldSat. try to factor common
   parts with checkHeaps and checkWorlds. *)

let checkHeapSat errList usedBoxes g heapEnv heapTyp =
  let errList =
    errList @ [spr "Sub.checkHeapSat:\n%s" (strHeapSat heapEnv heapTyp)] in

  (* step 1: check heap variables *)
  let ((hs1,cs1),(hs2,cs2)) = (heapEnv, heapTyp) in
  let (hs1,hs2) = (List.sort compare hs1, List.sort compare hs2) in
  if hs1 <> hs2 then
    die errList (spr
      "heap variables not the same:\n   %s\n!= %s"
      (String.concat "," hs1) (String.concat "," hs2));

  (* step 2: check structure of bindings and compute substitution *)
  let (subst,obligations) =
    List.fold_left (fun (acc1,acc2) (l,hc2) ->
      match findLocInHeapEnv l (snd heapEnv) with
        | None -> die errList (spr "location not found: %s" (strLoc l))
        | Some(hc1) ->
            begin match hc1, hc2 with
              | HEStrong(_,lo1,_),HStrong(_,_,lo2,_) when lo1 <> lo2 ->
                  die errList (spr "proto links differ: %s" (strLoc l))
              | HEStrong(v,_,_),HStrong(Some(x),t,_,_) ->
                  ((x, WVal v) :: acc1, (l, x, t) :: acc2)
              | HEStrong(v,_,_),HStrong(None,t,_,_) ->
                  (match maybeValOfSingleton t with
                     | Some(v') when v = v' -> (acc1, acc2)
                     | _ -> let x = freshVar "heapSatTemp" in
                            ((x, WVal v) :: acc1, (l, x, t) :: acc2))
              | HEWeak(x),HWeak(x') ->
                  if x = x' then (acc1, acc2) else
                  die errList (spr "thaw states differ: %s %s"
                    (strThawState x) (strThawState x'))
              | _ ->
                  die errList (spr "wrong shape for: %s" (strLoc l))
            end
      ) ([],[]) (snd heapTyp)
  in

  (* step 2b: allow frozen scalar references to be dropped *)
  List.iter (fun (l,hc1) ->
    if not (List.mem_assoc l (snd heapTyp)) then begin
      match hc1 with
        | _ -> () (* TODO *)
        | _ -> die errList (spr "can't drop binding for %s" (strLoc l))
    end
  ) (snd heapEnv);

  (* step 3: check the type of each binding *)
  List.iter (fun (l,x,t) ->
    let p = applyTyp t (wVar x) in
    let p = substForm (subst,[],[],[]) p in
    let errList' = errList @ [spr "Checking location [%s] ..." (strLoc l)] in
    checkFormula errList' usedBoxes g p
  ) obligations;

  subst

let checkWorldSat errList usedBoxes g (t,heapEnv) (s,heapTyp) =
  Zzz.inNewScope (fun () ->
    let (g,t) = bindExistentials g t in
    checkTypes errList usedBoxes g (Typ t) s;
    checkHeapSat errList usedBoxes g heapEnv heapTyp)


(***** Entry point ************************************************************)

let types cap g t s =
  Stats.time "Sub.types" (fun () ->
    checkTypes [spr "Sub.types: %s" cap] [] g t s)

let heapSat cap g h0 h =
  Stats.time "Sub.heapSat" (fun () ->
    checkHeapSat [spr "Sub.heapSat: %s" cap] [] g h0 h)

let worldSat cap g w0 w =
  Stats.time "Sub.worldSat" (fun () ->
    checkWorldSat [spr "Sub.worldSat: %s" cap] [] g w0 w)

(* let mustFlow   = mustFlow_ TypeTerms.empty
   let canFlow    = canFlow_ TypeTerms.empty

let mustFlowCache = Hashtbl.create 17
let mustFlowCounters = Hashtbl.create 17

let mustFlow ?filter:(filter=(fun _ -> true)) g t = 
  if !depth >= 0 && Hashtbl.mem mustFlowCache t then begin
    Hashtbl.replace mustFlowCounters t (1 + Hashtbl.find mustFlowCounters t);
    Hashtbl.find mustFlowCache t
  end else begin
    let boxes = mustFlow_ TypeTerms.empty ~filter g t in
    Hashtbl.add mustFlowCache t boxes;
    Hashtbl.add mustFlowCounters t 1;
    boxes
  end
*)

let writeStats () =
(*
  let oc = open_out (Settings.out_dir ^ "extract-cache.txt") in
  Hashtbl.iter (fun t _ ->
    let c = Hashtbl.find mustFlowCounters t in
    fpr oc "%s %d\n" (strTyp t) c
  ) mustFlowCache;
*)
  fpr oc_quick "Total Quick:      %4d\n" !count_quick;
  fpr oc_quick "Total Slow:       %4d\n" !count_slow;
  fpr oc_quick "-----------------------\n";
  fpr oc_quick "Total Subtypings: %4d" (!count_quick + !count_slow);
  ()

let mustFlowIterator   = mustFlowIterator_ []

