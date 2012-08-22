
open Lang
open LangUtils

let doMeet        = ref false
let maxJoinSize   = ref 1 (* anything <= 1 means not doing joins *)


(***** Collecting type terms, or "boxes" **************************************)

let typeTermsTyp acc t = (* naive way to compute this *)
  foldForm (fun acc -> function
    | PUn(HasTyp(_,u)) -> TypeTerms.add u acc
    | _                -> acc
  ) acc t

let typeTerms g =
  let init = TypeTerms.singleton UNull in
  List.fold_left (fun acc -> function
    | Var(x,t) ->
        (* since foldForm takes a type, jumping through TRefinement hoop *)
        let p = applyTyp t (wVar x) in
        typeTermsTyp acc (TRefinement ("DUMMY TYPE TERMS", p))
    | _ ->
        acc
  ) init g

(* 3/19 TODO hack since simpleSnapshot doesn't dive into arrows on the heap.
   running with -tryAllBoxes just tries all of them instead of what's
   in the current type env. sound, but slower. *)
let typeTerms g =
  if !Settings.tryAllBoxesHack then
    List.fold_left
      (fun acc i -> TypeTerms.add (Utils.IdTable.getVal idTypTerms i) acc)
      TypeTerms.empty (Utils.list1N (Utils.IdTable.size idTypTerms))
  else
    typeTerms g

let typeTerms g =
  BNstats.time "typeTerms" typeTerms g


(***** Meet/Join **************************************************************)

let meet u1 u2 = failwith "meet nyi"

let join u1 u2 = failwith "join nyi"

let combineArrows f boxes =
  TypeTerms.fold (fun ut acc ->
    match ut, acc with
      | UArrow _, None    -> Some ut
      | UArrow _, Some(u) -> Some (f ut u)
      | _                 -> acc
  ) boxes None

let meetAll = combineArrows meet
let joinAll = combineArrows join


(***** Type extraction, or "unboxing" *****************************************)

let boxNumbers s = 
  let l = TypeTerms.elements s in
  let il =
    List.map (function ut ->
      try Utils.IdTable.getId idTypTerms ut
      with Not_found -> failwith (spr "Sub.boxNumbers:\n\n %s" (prettyStrTT ut))
    ) l in
  il

let setUpExtract t usedBoxes =
  let x = freshVar "extract" in
  (* Zzz.pushScope (); *)
  Zzz.addBinding x t;
  Zzz.dump (spr "; off limits: %s" (Utils.strIntList (boxNumbers usedBoxes)));
  Zzz.doingExtract := true;
  x

let tearDownExtract () =
  Zzz.doingExtract := false;
  (* Zzz.removeBinding (); *)
  (* Zzz.popScope (); *)
  ()

let mustFlow_ usedBoxes ?filter:(f=(fun _ -> true)) g t =
  (* Log.smallTitle "MustFlow"; *)
  let boxes = TypeTerms.diff (typeTerms g) usedBoxes in
  let boxes = TypeTerms.filter f boxes in
  let boxes = TypeTerms.add UNull boxes in (* 3/15 *)
  Zzz.inNewScope (fun () ->
    let x = setUpExtract t usedBoxes in
    (*
    let extracted =
      TypeTerms.fold
        (fun ut acc ->
           if Zzz.checkValid "mustFlow" (hastyp (wVar x) ut)
             then TypeTerms.add ut acc
             else acc)
        boxes
        TypeTerms.empty
    in
    *)
    (* 4/1: once a Ref term is extracted, don't try any more *)
    let (_,extracted) =
      TypeTerms.fold
        (fun ut (stop,acc) ->
           if not stop && Zzz.checkValid "mustFlow" (hastyp (wVar x) ut) then
             let stop = match ut with URef _ -> true | _ -> false in
             (stop, TypeTerms.add ut acc)
           else
             (stop, acc))
        boxes
        (false, TypeTerms.empty)
    in
    tearDownExtract ();
    let il = boxNumbers extracted in
    Zzz.dump (spr "; extracted: is(%s, %s)" x (Utils.strIntList il));
    (* Log.log (spr "%s\n" (Utils.strIntList il)); *)
    extracted)

let mustFlow_ usedBoxes ?filter:(f=(fun _ -> true)) g t =
  BNstats.time "mustFlow_" (mustFlow_ usedBoxes ~filter:f g) t

let canFlow_ usedBoxes ?filter:(f=(fun _ -> true)) g t =
  (* Log.smallTitle "CanFlow"; *)
  let boxes = TypeTerms.diff (typeTerms g) usedBoxes in
  let boxes = TypeTerms.filter f boxes in
  Zzz.inNewScope (fun () ->
    let x = setUpExtract t usedBoxes in
    (* subsets of size 1 to !maxJoinSize in increasing order of size *)
    let subsets =
      boxes
      |> TypeTerms.elements
      |> Utils.powersetMaxSize !maxJoinSize
      (* |> List.filter (fun l -> List.length l > 1) *)
      |> List.sort (fun l1 l2 -> List.length l1 - List.length l2)
    in
    let extracted =
      try
        List.find (function subset ->
          let upperBound = pOr (List.map (hastyp (wVar x)) subset) in
          Zzz.checkValid "canFlow" upperBound
        ) subsets
      with Not_found ->
        []
    in
    tearDownExtract ();
    mkTypeTerms extracted)


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

let strHeapSat (hs1,cs1) (hs2,cs2) =
  let s0 = spr "  %s |= %s" (String.concat "++" hs1) (String.concat "++" hs2) in
  let l1 = List.map (fun (l,hc) ->
             spr "  %s |-> %s |= %s" (strLoc l)
               (if List.mem_assoc l cs1
                then prettyStr strHeapEnvCell (List.assoc l cs1)
                else "MISSING")
               (prettyStr strHeapCell hc)) cs2 in
  let l2 = List.map (fun (l,hc) ->
            if List.mem_assoc l cs2 then ""
            else spr "  %s |-> %s |= MISSING"
                   (strLoc l) (prettyStr strHeapEnvCell hc)) cs1 in
  let l2 = List.filter (fun s -> s <> "") l2 in
  String.concat "\n" [s0; String.concat "\n" l1; String.concat "\n" l2]
  
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


(***** Subtyping **************************************************************)

let rec bindExistentials errList = function
  | TExists(x,s1,s2) ->
      (match s1 with
         | TExists _ -> die errList "Sub.bindExistentials: not prenex form"
         | _ ->
             (* let _ = Log.log2 "bind %s :: %s\n" x (prettyStrTyp s1) in *)
             let _ = Zzz.addBinding x s1 in
             let (n,s) = bindExistentials errList s2 in
             (1 + n, s))
  | s -> (0, s)

let rec checkTypes errList usedBoxes g t1 t2 =
  let errList =
    errList @ [spr "Sub.checkTypes:\n   t1 = %s\n   t2 = %s"
                 (prettyStrTyp t1) (prettyStrTyp t2)] in
  let _ =
    match t2 with
      | TExists _ -> die errList "existential type on the right"
      | _ -> () in
  Zzz.inNewScope (fun () ->
    let (n,t1) = bindExistentials errList t1 in
    let v = freshVar "v" in
    Zzz.addBinding v t1;
    checkFormula errList usedBoxes g (applyTyp t2 (wVar v));
(*
    (* remove v and existential binders from curScope *)
    Zzz.removeBinding ();
    for i = 1 to n do Zzz.removeBinding () done;
*)
    ()
  )

and checkFormula errList usedBoxes g p =
  let clauses = Cnf.convert p in
  let n = List.length clauses in
  Utils.iter_i
    (fun (pi,qi) i ->
       Zzz.inNewScope (fun () ->
         Zzz.assertFormula pi;
         let qForm = pOr (List.map (fun q -> PUn q) qi) in
         let (s1,s2) = (prettyStrForm pi, prettyStrForm qForm) in
         let errList =
           errList @ [spr "Clause %d/%d:\n   %s\n~> %s" (i+1) n s1 s2] in
         checkUnPreds errList usedBoxes g (qi,qForm)))
    clauses

(* small optimization: qForm is qs lifted to a formula, since qForm is
   already computed by checkFormula for printing purposes *)
and checkUnPreds errList usedBoxes g (qs,qForm) =
  if Zzz.checkValid "I-Valid" qForm then ()
  else if List.exists (checkUnPred errList usedBoxes g) qs then ()
  else die errList "Cannot discharge this clause."

and checkUnPred errList usedBoxes g = function
  | HasTyp(w,u) -> checkHasTyp errList usedBoxes g w u 

and checkHasTyp errList usedBoxes g w u =
(*
  let errList =
    errList @ [spr "checkHasTyp %s :: %s" (prettyStrWal w) (prettyStrTT u)] in
*)

  if !maxJoinSize = 1 then begin
    let mustFlowBoxes = mustFlow_ usedBoxes g (ty(PEq(theV,w))) in
    let usedBoxes = TypeTerms.union usedBoxes mustFlowBoxes in
    let n = TypeTerms.cardinal mustFlowBoxes in
    if n = 0 then die errList (spr "0 boxes must-flow to %s" (prettyStrWal w))
    else if n > 0 && !doMeet then die errList "meet nyi"
    else TypeTerms.exists
           (function u' -> checkTypeTerms errList usedBoxes g u' u)
           mustFlowBoxes

  end else begin
    let smallestCanFlowSet = canFlow_ usedBoxes g (ty(PEq(theV,w))) in
    ignore smallestCanFlowSet;
    die errList "join nyi!"
  end

and checkTypeTerms errList usedBoxes g u1 u2 =
  sugarArrow := false;
  let errList =
    errList @ [spr "checkTypeTerms:\n   %s\n<: %s"
                 (prettyStrTT u1) (prettyStrTT u2)] in
  sugarArrow := true;
  match u1, u2 with
    | UVar(x), UVar(y) -> x = y
    | URef(x), URef(y) -> x = y
    (* 3/15 *)
    | UNull, URef(y)   -> isWeakLoc y
    | UArrow(arr1), UArrow(arr2) -> checkArrow errList usedBoxes g arr1 arr2
    | UArray(t1), UArray(t2) ->
       (try (* TODO 3/10 ideally want a version that returns bool instead
               of failing *)
         let _ = checkTypes errList usedBoxes g t1 t2 in
         let _ = checkTypes errList usedBoxes g t2 t1 in
         true
       with Tc_error _ ->
         false)
    | _ -> die errList "Syntactic types don't match up."

and checkArrow errList usedBoxes g
      ((ts1,ls1,hs1),x1,t11,e11,t12,e12) ((ts2,ls2,hs2),x2,t21,e21,t22,e22) =

  failwith "Sub.checkArrow"

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
              (* simple locations *)
              | HEConc(v),HConc(Some(x),t) ->
                  ((x, WVal v) :: acc1, (l, x, t) :: acc2)
              | HEConc(v),HConc(None,t) ->
                  begin match maybeValOfSingleton t with
                    | Some(v') when v = v' -> (acc1, acc2)
                    | _ -> let x = freshVar "heapSatTemp" in
                           ((x, WVal v) :: acc1, (l, x, t) :: acc2)
                  end
              (* object locations *)
              | HEConcObj(_,l'),HConcObj(_,_,l'') when l' <> l'' ->
                  die errList (spr "proto links differ: %s" (strLoc l))
              | HEConcObj(v,_),HConcObj(Some(x),t,_) ->
                  ((x, WVal v) :: acc1, (l, x, t) :: acc2)
              | HEConcObj(v,_),HConcObj(None,t,_) ->
                  begin match maybeValOfSingleton t with
                    | Some(v') when v = v' -> (acc1, acc2)
                    | _ -> let x = freshVar "heapSatTemp" in
                           ((x, WVal v) :: acc1, (l, x, t) :: acc2)
                  end
              (* weak locations *)
              | HEWeakTok(x),HWeakTok(x') ->
                  if x = x' then (acc1, acc2) else
                  die errList (spr
                    "thaw states differ: %s %s"
                    (strThawState x) (strThawState x'))
              | _ ->
                  die errList (spr "wrong shape for: %s" (strLoc l))
            end
      ) ([],[]) (snd heapTyp)
  in

  (* TODO when existential locations are added, don't allow any
     locations to be dropped *)

  (* step 3: check the type of each binding *)
  List.iter (fun (l,x,t) ->
    let p = applyTyp t (wVar x) in
    let p = substForm (subst,[],[],[]) p in
    let errList' = errList @ [spr "Checking location [%s] ..." (strLoc l)] in
    checkFormula errList' usedBoxes g p
  ) obligations;

  subst

let checkWorldSat errList usedBoxes g (t,heapEnv) (s,heapTyp) =
  checkTypes errList usedBoxes g t s;
  checkHeapSat errList usedBoxes g heapEnv heapTyp


(***** Entry point ************************************************************)

let types cap = checkTypes [spr "Sub.types: %s" cap] TypeTerms.empty
let heapSat cap = checkHeapSat [spr "Sub.heapSat: %s" cap] TypeTerms.empty
let worldSat cap = checkWorldSat [spr "Sub.worldSat: %s" cap] TypeTerms.empty

let mustFlow   = mustFlow_ TypeTerms.empty

let mustFlowCache = Hashtbl.create 17
let mustFlowCounters = Hashtbl.create 17

(*
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

let writeCacheStats () =
  let oc = open_out (Settings.out_dir ^ "extract-cache.txt") in
  Hashtbl.iter (fun t _ ->
    let c = Hashtbl.find mustFlowCounters t in
    fpr oc "%s %d\n" (strTyp t) c
  ) mustFlowCache

let canFlow    = canFlow_ TypeTerms.empty

