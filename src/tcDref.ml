
open Lang
open LangUtils
open TcUtils


(**** Environment operations **************************************************)

let removeLabels g =
  List.filter (function Lbl _ -> false | _ -> true) g

let printBinding (x,s) =
  if !Settings.printAllTypes || !depth = 0 then begin
    setPretty true;
    pr "\n%s :: %s\n" x (strTyp s);
    setPretty false;
    flush stdout;
    ()
  end


(* TODO should be factored somewhere, since Wf does something similar *)
let depTupleBinders t =
  let rec foo acc = function
    | TTuple(l) -> 
        let (xs,ts) = List.split l in
        let acc = List.fold_left (fun acc x -> x::acc) acc xs in
        List.fold_left foo acc ts
    | TNonNull(t) | TMaybeNull(t) -> foo acc t
    | _ -> acc
  in foo [] t


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

(* TODO why does this need to take in h? just for printing? *)

let tcAddBinding ?(printHeap=true) ?(isNew=true) g h x s =

  let (n,g) = addDepTupleBindings g s in

  Zzz.addBinding ~isNew x (applyTyp s (wVar x));
  printBinding (x,s);
  let g = Var(x,s)::g in
(*
  let (g,h) = tryDestruct g h x s in (* unfolding with new env that x:s *)
*)
  (* unfolding with new env that has x:s *)
(*
  tryUnfold g (x,s);
*)
  if !Settings.printAllTypes || !depth = 0 then begin
    if printHeap
    then pr "/ %s\n" (prettyStr strHeap h)
    else ()
  end;
  (succ n, g)

(*
let tcRemoveBinding () =
  Zzz.removeBinding ();
  ()
*)

let tcAddTypeVar x g =
  Zzz.addTypeVar x;
  TVar(x)::g

let tcRemoveTypeVar () =
  Zzz.removeBinding ();
  ()

let tcRemoveBindingN n =
(*
  for i = 1 to n do tcRemoveBinding () done
*)
  for i = 1 to n do Zzz.removeBinding () done


(***** Heap operations ********************************************************)

(* TODO avoid snapshotting unchanged bindings more than once *)

let snapshot g h =
  let l = List.map snd (snd h) in
  let add = tcAddBinding ~printHeap:false in
  let (n,g1) = 
    List.fold_left (fun (k,acc) -> function
      | HConc(x,t) | HConcObj(x,t,_) ->
          let (i,g) = add acc h x tyAny in
          (* TODO 11/27: doing this so all the dep tuple binders get declared. *)
          let ys = depTupleBinders t in
          List.fold_left
            (fun (k,acc) y -> let (j,g) = add acc h y tyAny in (k+j, g))
            (i,g) ys
    ) (0,g) l
  in
  let g2 = 
    List.fold_left (fun acc -> function
      (* TODO: here's one obvious place where binders are getting redefined *)
      | HConc(x,s) | HConcObj(x,s,_) -> snd (add ~isNew:false acc h x s)
    ) g1 l
  in
  (n, g2)


let freshenWorld (t,(hs,cs)) =
  let vSubst =
    List.map
      (function (_,HConc(x,_)) | (_,HConcObj(x,_,_)) -> (x, freshVar x)) cs in
  let subst = (List.map (fun (x,y) -> (x, wVar y)) vSubst, [], [], []) in
  let (fresh,cs) =
    List.fold_left (fun (acc1,acc2) -> function
      | (l,HConc(x,s)) ->
          let x' = List.assoc x vSubst in
          let s' = masterSubstTyp subst s in
          ((x',s')::acc1, (l,HConc(x',s'))::acc2)
      | (l,HConcObj(x,s,l')) ->
          let x' = List.assoc x vSubst in
          let s' = masterSubstTyp subst s in
          ((x',s')::acc1, (l,HConcObj(x',s',l'))::acc2)
    ) ([],[]) cs in
  let t = masterSubstTyp subst t in
  (fresh, (t, (hs, cs)))

let selfifyHeap (hs,cs) =
  let (fresh,cs) =
    List.fold_left (fun (acc1,acc2) -> function
      | (l,HConc(x,s)) ->
          let x' = freshVar x in
          ((x',s)::acc1, (l, HConc (x', ty (PEq (theV, wVar x))))::acc2)
      | (l,HConcObj(x,s,l')) ->
          let x' = freshVar x in
          ((x',s)::acc1, (l, HConcObj (x', ty (PEq (theV, wVar x)), l'))::acc2)
    ) ([],[]) cs
  in
  (fresh, (hs, cs))

(* both findHeapCell functions look for the first matching constraint *)

let findHeapCell l (_,cs) =
  try Some (snd (List.find (fun (l',_) -> l = l') cs))
  with Not_found -> None

let findAndRemoveHeapCell l (hs,cs) =
  match findHeapCell l (hs,cs) with
    | Some(cell) -> Some (cell, (hs, List.remove_assoc l cs))
    | None       -> None

let splitHeapAround h l = failwith "splitHeapAround"
(*
let splitHeapAround h l =
  let rec foo prefix = function
    | []                      -> None
    | (l',hc)::tl when l = l' -> Some (prefix, hc, tl)
    | (l',hc)::tl             -> foo (prefix @ [l',hc]) tl
  in
  foo [] h
*)

let splitHeapForCall _ _ = failwith "splitHeapForCall"
(*
(* partitioning the heap h by walking in order, and selecting the elements
   that match the domain of h11 *)
let splitHeapForCall h h11 =
(*
  let dom = List.map fst h11 in
  let (h2,h1) = List.partition (fun (l,_) -> List.mem l dom) h in
  (h1, h2)
*)
  let (h1,h2) =
    List.fold_left (fun (h1,h2) hc ->
      let l = match hc with HAbs(l,_) | HConc(l,_,_) -> l in
      if List.mem l (Wf.domH h11)
        then (h1, hc::h2)
        else (hc::h1, h2)
    ) ([],[]) h
  in
  (List.rev h1, List.rev h2)
*)

let checkLocActuals _ _ _ = failwith "checkLocActuals"
(*
let checkLocActuals cap lf la =
  let err s = err (spr "%s: %s" cap s) in
  let (n,m) = List.length lf, List.length la in
  if n <> m then err (spr "got %d loc actuals but expected %d" m n)
  else match Utils.someDupe la with
    | Some(x) -> err (spr "[%s] duplicate" x)
    | None    -> List.combine lf la
*)


(***** Var elimination for let rules ******************************************)

(* stop checking heap well-formedness at the EHeap exp *)
let checkWfHeap = ref true

(* TODO 11/22 *)

let rec mkExists s = function
  | (x,t)::l -> TExists (x, t, mkExists s l)
  | []       -> s

let finishLet cap g y l (s,h) =
  (* TODO: 11/26 hack so that EHeap works w/o change *)
  if y = "end_of_pervasives" then checkWfHeap := false;

  if not !Settings.tryElimLocals then (s, h)
  else begin
(*
    if y = "begin_main" then checkWfHeap := false;
    let s = List.fold_left (fun acc (x,s1) -> elimLocalTyp x s1 acc) s l in
    let h = List.fold_left (fun acc (x,s1) -> elimLocalHeap x s1 acc) h l in
    if !checkWfHeap then Wf.world (spr "finishLet: %s" cap) g (s,h);
    (s, h)
*)
    let w = (mkExists s l, h) in
    (* alg typing should now synthesize only wf worlds b/c of existentials. 
       but doing this as a sanity check. *)
    if !checkWfHeap then Wf.world (spr "finishLet: %s" cap) g w;
    w
  end


(***** Misc operations ********************************************************)

(* TODO when adding abstract refs, revisit these two *)

let refTermsOf g t =
  let isConcRef = function URef _ -> true | _ -> false in
  TypeTerms.elements (Sub.mustFlow g t ~filter:isConcRef)

let singleRefTermOf cap g t =
  match refTermsOf g t with
    | [URef(l)] -> l
    | []        -> err ([cap; "0 ref terms flow to value"])
    | l         -> err ([cap; "multiple ref terms flow to value";
                         String.concat ", " (List.map prettyStrTT l)])

let ensureSafeWeakRef cap g t =
  failwith "ensureSafeWeakRef"
(*
  let safe = TRefinement ("v", PNot (PEq (theV, aNull))) in
  Sub.checkTypes cap g TypeTerms.empty t safe
*)


(***** TC helpers *************************************************************)

let oc_wrap_goal = open_out (Settings.out_dir ^ "wrap_goal.txt")

(* 9/27 switching this to world instead of annot *)
let wrapWithGoal cap x e w =
  failwith "wrapWithGoal"
(*
  let y = spr "wrapWithGoal_%s" x in
  fpr oc_wrap_goal "%s\n%s \nsGoal = %s\n\n" y cap (prettyStr strWorld w);
  EAs (y, e, w)
*)

(*
let strFrame (h1,(s2,h2)) =
  spr "    %s\n -> %s\n  / %s"
    (prettyStrHeap h1) (prettyStrScm s2) (prettyStrHeap h1)
*)

let applyFrame hAct (ls,h1,(t2,h2)) =
  match ls with
    | [x] when h1 = ([x],[]) && h1 = h2 -> (t2, hAct)
    | _ -> failwith "applyFrame: need to implement general case"

(*
let applyFrame g h (h11,(s,h12)) =
  failwith "applyFrame"
*)
(*
  let (h0,h1) = splitHeapForCall h h11 in
  let subst = niceCheckHeaps ["SHOULD PASS CAPS TO applyFrame"] g h1 h11 in
(*
  (* TODO freshen heap ? *)
  (h0, (applyVarSubstScm subst s, applyVarSubstHeap subst h12))
*)
  (* TODO 9/28 *)
  (h0, (applyVarSubstScm subst s, snd (freshen (applyVarSubstHeap subst h12))))
*)

(*
(* this won't be needed if just remove AScm eventually. then applyFrame
   can be used directly instead of applyAnnotation. *)
let applyAnnotation g h = function
  | AScm(s)   -> applyFrame g h ([],(s,[]))
  | AFrame(f) -> applyFrame g h f
*)


(***** TC lambda helpers ******************************************************)

let isArrow = function
  | TRefinement(x,PUn(HasTyp(y,UArr(arr)))) when y = wVar x -> Some arr
  | THasTyp(UArr(arr)) -> Some arr
  | _ -> None

let isArrows t =
  match isArrow t, t with
    | Some(arr), _ -> Some [arr]
    | None, TRefinement(x,PConn("and",ps)) ->
        List.fold_left (fun acc p ->
          match acc, p with
            | Some(l), PUn(HasTyp(y,UArr(arr))) when y = wVar x -> Some(arr::l)
            | _ -> None
        ) (Some []) ps
    | _ -> None

type app_rule_result =
  | AppOk   of (vvar * typ) list * world
  | AppFail of string list

let maybeInferHeapParam cap curHeap hActs hForms e11 =
  match hActs, hForms, e11 with

    | [], [x], _ when e11 = ([x],[]) -> Some curHeap

    (* more general than the previous case. the inferred heap arg is
       all of curHeap except the location constraint corresponding to
       the formal heap location constraints. *)
    | [], [x], ([x'],cs1) when x = x' ->
        let (hs,cs) = curHeap in
        Some (hs, List.filter (fun (l,_) -> not (List.mem_assoc l cs1)) cs)

    | _ -> None

(* TODO

    | [x], ([x'],_), ([x''],_) when x = x' && x = x'' ->
        err [cap;
             "ts eletapp: TODO heap instantiation";
             spr "hForms = %s" (String.concat "," hForms);
             spr "e11 = %s" (prettyStrHeap e11);
             spr "e12 = %s" (prettyStrHeap e12)]
    | _ ->
        let s = "[...; ...; H] x:T1 / [H ++ ...] -> T2 / [H ++ ...]" in
        err [cap; spr "arrow not of the form %s" s;
                  prettyStrHeap e11;
                  prettyStrHeap e12]
*)

let maybeInferHeapParam cap curHeap hActs hForm e11 =
  let eo = maybeInferHeapParam cap curHeap hActs hForm e11 in
(*
  begin match eo with
    | None -> ()
    | Some(e) -> pr "inferred heap act: %s\n\n for input heap: %s"
                   (prettyStrHeap e) (prettyStrHeap e11)
  end;
*)
  eo

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
    | TNonNull(t) | TMaybeNull(t) -> failwith "depTupleSubst: null"
    | _ -> acc
  in
  let subst = foo w [] t in
  subst

let heapDepTupleSubst (_,cs) =
  let rec foo path acc = function
    | TTuple(l) ->
        Utils.fold_left_i (fun acc (x,t) i ->
          let path = sel path (wProj i) in
          let acc = foo path acc t in
          (x, path) :: acc
        ) acc l
    | TNonNull(t) | TMaybeNull(t) -> failwith "heapDepTupleSubst: null"
    | _ -> acc
  in
  let subst =
    List.fold_left (fun acc -> function
      | (_,HConc(x,s)) | (_,HConcObj(x,s,_)) -> foo (wVar x) acc s
    ) [] cs
  in
(*
List.iter (fun (x,w) -> pr "ravi %s |-> %s\n" x (prettyStrWal w)) subst;
*)
  subst


(***** Bidirectional type checking ********************************************)

let initHeapSet = ref false

(***** Initial trivial checks *****)

let rec tsVal g h e =
  if Zzz.falseIsProvable "tsVal" then tyFls
  else tsVal_ g h e

and tsExp g h e =
  if Zzz.falseIsProvable "tsExp" then (tyFls, botHeap)
  else tsExp_ g h e

and tcVal g h s e =
  if Zzz.falseIsProvable "tcVal" then ()
  else tcVal_ g h s e

and tcExp g h w e =
  if Zzz.falseIsProvable "tcExp" then ()
  else tcExp_ g h w e


(***** Value type synthesis ***************************************************)

and tsVal_ g h = function

  | VBase(Null) -> tyNull

  | (VBase _ as v) | (VEmpty as v) -> ty (PEq (theV, WVal v))

  (* TODO any benefit to using upd instead of VExtend? *)
  | (VExtend(v1,v2,v3) as v) -> begin
      tcVal g h tyDict v1;
      tcVal g h tyStr v2;
      ignore (tsVal g h v3);
      ty (PEq (theV, WVal v))
    end

  | VVar(x) -> begin
      try
        let _ = List.find (function Var(y,_) -> x = y | _ -> false) g in
        ty (PEq (theV, wVar x))
      with Not_found ->
        err [spr "ts: var not found: [%s]" x]
    end

  | VFun(l,x,Some(t1,h1),e) -> begin
      failwith "ts VFun"
(*
      let g = removeLabels g in
      (* TODO unfortunately duplicating some work of UArrImp, since
         don't want to check the synthesized return type here... *)
      Wf.wfLocFormalsFail "ts annotated VFun" l;
      Wf.wfHeapFail "ts annotated VFun: h1" g h1;
      Wf.wfTypFail "ts annotated VFun: t1" g h1 t1;
      Zzz.pushScope ();
      let (n,g) = snapshot g h1 in 
      let (g,h1) = tcAddBinding g h1 x (STyp t1) in
      let (t2,h2) =
        match tsExp g h1 e with
          | STyp(t2),h2 -> (t2, h2)
          | _           -> err "ts VFun: t2"
      in
      tcRemoveBinding ();
      tcRemoveBindingN n;
      Zzz.popScope ();
      let t = tyArrImp l x t1 h1 t2 h2 in
(*
      Wf.wfTypFail "VFunImp" g t;
*)
      STyp t
*)
    end

  | VFun(l,x,None,e) -> failwith "ts bare VFun"
      (* tsVal g h (VFun(l,x,Some(tyAny,[]),e)) *)

  | VArray(t,vs) ->
      let n = List.length vs in
      ty (pAnd (
        hastyp theV (UArray t)
        :: PPacked theV :: PEq (arrlen theV, wInt n)
        :: (Utils.map_i (fun vi i -> PEq (sel theV (wInt i), WVal vi)) vs)))


(***** Expression type synthesis **********************************************)

and tsExp_ g h = function

  | EVal(v) -> (tsVal g h v, h)

  | ELet(x,None,ENewref(l,EVal(v)),e) -> begin
      let ruleName = "TS-LetNewref" in
      let strE =
        spr "  let %s = ref %s (%s) in ..." x (strLoc l) (prettyStrVal v) in
      match findHeapCell l h with
        | Some(HConc _)
        | Some(HConcObj _) ->
            err ([spr "%s-Strong: %s" ruleName strE;
                  spr "location [%s] already bound" (strLoc l)])
        | None -> begin
            (* TODO should also check dead locations *)
            let s0 = tsVal g h v in
            let y = freshVar "hc" in
            let h1 = (fst h, snd h @ [(l, HConc (y, s0))]) in
            let s1 = tyRef l in
            let (n,g) = tcAddBinding g h1 y s0 in
            let (m,g) = tcAddBinding g h1 x s1 in
            let (s2,h2) = tsExp g h1 e in
(*
            tcRemoveBinding ();
            tcRemoveBinding ();
*)
            tcRemoveBindingN (n + m);
            let cap = spr "%s-Strong: %s" ruleName strE in
            finishLet cap g x [(y,s0);(x,s1)] (s2,h2)
          end
(*
      let ruleName = "TS-LetNewref" in
      let strE = spr "  let %s = ref %s (%s) in ..." x l (prettyStrVal v) in
      let err s = niceError [ruleName; strE; s] in
      match findHeapCell l h with
      | Some(HConc _) ->
          err (spr "concrete location [%s] already bound" l)
      | Some(HAbs(_,s)) -> begin
          tcVal g h s v;
          let sRef = STyp (tyIsBang theV (URef(l))) in
          let (g,h) = tcAddBinding g h x sRef in
          let (s2,h2) = tsExp g h e in
          tcRemoveBinding ();
          finishLet [ruleName ^ "-Weak"; strE] g x [(x,sRef)] (s2,h2)
        end
      | None -> begin
          (* TODO should also check dead locations *)
          (* TODO might also want a way to create as abstract, with
               weaker invariant *)
          let s0 = tsVal g h v in
          let y = freshVar "hc" in
          let h1 = h @ [HConc (l, y, s0)] in
          let s1 = STyp (tyIsBang theV (URef(l))) in
          let (g,h1) = tcAddBinding g h1 y s0 in
          let (g,h1) = tcAddBinding g h1 x s1 in
          let (s2,h2) = tsExp g h1 e in
          tcRemoveBinding ();
          finishLet [ruleName ^ "-Strong"; strE] g x [(y,s0);(x,s1)] (s2,h2)
        end
*)
    end

  | EDeref(EVal(v)) -> begin
      let cap = spr "TS-Deref: !(%s)" (prettyStrVal v) in
      let t1 = tsVal g h v in
      let l = singleRefTermOf cap g t1 in
      match findHeapCell l h with
        | Some(HConc(y,s)) -> (ty (PEq (theV, wVar y)), h)
        | Some(HConcObj _) -> err ([cap; "not handling ConcObj cell"])
        | None -> err ([cap; spr "unbound loc [%s]" (strLoc l)])
                     
(*
      let ruleName = "TS-Deref" in
      let strE = spr "  !(%s) " (prettyStrVal v) in
      let err s = niceError [ruleName; strE; s] in
      match tsVal g h v with STyp(t1) -> begin
        match refTermsOf g t1 with [URef(l)] -> begin
          match findHeapCell l h with
            | Some(HConc(_,y,s)) -> (selfify y s, h)
            | Some(HAbs(_,s))    -> (ensureSafeWeakRef "ts EDeref" g t1; (s, h))
            | None               -> err (spr "unbound loc [%s]" l)
        end
        | _ -> err (spr "[%s] should have exactly 1 ref term" (strValue v))
      end
      | _ -> err "should be a monotype"
*)
    end

  | ELet(x,None,ESetref(EVal(v1),EVal(v2)),e) -> begin
      let (s1,s2) = (prettyStrVal v1, prettyStrVal v2) in
      let cap = spr "TS-LetSetref: let %s = (%s) := (%s)" x s1 s2 in
      let t1 = tsVal g h v1 in
      let s2 = tsVal g h v2 in
      let l = singleRefTermOf cap g t1 in
      match findAndRemoveHeapCell l h with
        | None -> err ([cap; spr "unbound loc [%s]" (strLoc l)])
        | Some(HConcObj _, _) -> err ([cap; "not handling ConcObj cell"])
        | Some(HConc(y,s), (hs,cs)) -> begin
            Wf.heap cap g (hs,cs);
            let y2 = freshVar y in
            let h1 = (hs, cs @ [(l, HConc (y2, s2))]) in
            let (n,g) = tcAddBinding ~printHeap:false g h1 y2 s2 in
            let (m,g) = tcAddBinding g h1 x s2 in
            let (s3,h3) = tsExp g h1 e in
(*
            tcRemoveBinding ();
            tcRemoveBinding ();
*)
            tcRemoveBindingN (n + m);
            finishLet cap g x [(y2,s2);(x,s2)] (s3,h3)
          end
(*
      let ruleName = "TS-LetSetref" in
      let strE = spr "  let %s = (%s) := (%s) in ..."
                    x (prettyStrVal v1) (prettyStrVal v2) in
      let err s = niceError [ruleName; strE; s] in
      match tsVal g h v1 with STyp(t1) -> begin
        match refTermsOf g t1 with [URef(l)] -> begin
          match findAndRemoveHeapCell l h with
          | Some(HConc(_,y,s)),h0 -> begin
              let h00 = h0 @ [HAbs (l, STyp tyAny)] in
              Wf.wfHeapFail (spr "ts ELetSetref strong [%s]: h00" x) g h00;
              let s' = tsVal g h v2 in
              let y' = freshVar y in
              let h1 = h0 @ [HConc (l, y', s')] in
              let (g,h1) = tcAddBinding ~printHeap:false g h1 y' s' in
              let (g,h1) = tcAddBinding g h1 x s' in
              let (s2,h2) = tsExp g h1 e in
              tcRemoveBinding ();
              finishLet [ruleName; strE] g x [(y',s');(x,s')] (s2,h2)
            end
          | Some(HAbs(_,s)),_ -> begin
              ensureSafeWeakRef (spr "ts LetSetref [%s]" x) g t1;
              tcVal g h s v2;
              let (g,h) = tcAddBinding g h x s in
              let (s3,h3) = tsExp g h e in
              tcRemoveBinding ();
              finishLet [ruleName; strE] g x [(x,s)] (s3,h3)
            end
          | None,_ -> err (spr "unbound loc [%s]" l)
        end
        | _ -> err "should have exactly 1 conc ref term"
      end
      | _ -> err "should be a monotype"
*)
    end

  | ELet(x,None,EApp(l,EVal(v1),EVal(v2)),e) -> begin
      let t1 = tsVal g h v1 in
      let boxes = TypeTerms.elements (Sub.mustFlow g t1) in
      let (s1,s2) = (prettyStrVal v1, prettyStrVal v2) in
      let cap = spr "TS-LetApp: let %s = [...] (%s) (%s)" x s1 s2 in
      tsELetAppTryBoxes cap g h x l v2 e boxes
(*
      let ruleName = "TS-LetApp" in
      let strE = spr "  let %s = (%s) <%s> (%s) in ..." x
        (prettyStrVal v1) (strLocs la) (prettyStrVal v2) in
      match tsVal g h v1 with
        | STyp(t1) ->
            let boxes = Sub.mustFlow g t1 TypeTerms.empty in
            let boxes = TypeTerms.elements boxes in
            tsELetAppTryBoxes strE g h x (v1,la,v2) e boxes
        | SAll _ ->
            niceError [ruleName; strE; "func has poly type"]
*)
    end

  | ELet(x,Some(f),EApp(l,EVal(v1),EVal(v2)),e) -> begin
      failwith "todo ts letapp with ann"
    end

(*
  | EFreeze(l,so) -> begin
      let cap = spr "ts EFreeze [%s] " l in
      let err s = err (spr "%s: %s" cap s) in
      match findAndRemoveHeapCell l h with
        | None,_ -> err "location not found"
        | Some(HAbs _),_ -> err "location is already non-linear"
        | Some(HConc(_,_,s')),h1 -> begin
            Wf.wfHeapFail cap g h1;
            let s =
              match so with
                | None    -> s'
                | Some(s) -> let _ = Sub.checkSchemes cap g s' s in s
            in
            let h' = h1 @ [HAbs (l, s)] in
            (STyp tyAny, h')
          end
    end
*)

  | ELet(x,None,ENewObj(l1,l2,EVal(v)),e) -> begin
      let cap = spr "TS-LetNewObj: new %s %s" (strLoc l1) (strLoc l2) in
      match findHeapCell l1 h, findHeapCell l2 h with
        | Some _, _ -> err [cap; spr "loc [%s] already bound" (strLoc l1)]
        | None, Some(HConcObj _) -> begin
            tcVal g h (tyRef l2) v;
            let y = freshVar "newobj" in
            let t = ty (PEq (theV, WVal VEmpty)) in
            let s = tyRef l1 in
            let h1 = (fst h, snd h @ [l1, HConcObj (y, t, l2)]) in
            let (n,g) = tcAddBinding ~printHeap:false g h1 y t in
            let (m,g) = tcAddBinding g h1 x s in
            let (s2,h2) = tsExp g h1 e in
(*
            tcRemoveBinding ();
            tcRemoveBinding ();
*)
            tcRemoveBindingN (n + m);
            finishLet cap g x [(y,t);(x,s)] (s2,h2)
          end
        | None, Some _ -> err [cap; spr "loc [%s] isn't a conc obj" (strLoc l2)]
        | None, None -> err [cap; spr "loc [%s] isn't bound" (strLoc l2)]
    end

  (* TODO 11/29: should just move to using existentials everywhere instead
     of the specialized let rules.
     tweaking ANF to not introduce as many let bindings, so trying to cope
     with the typing rules that require binding forms... *)
(*
  | ELet(x,None,e1,EVal(VVar(x'))) when x = x' ->
      let (t1,h1) = tsExp g h e1 in
      (TExists (x, t1, ty (PEq (theV, wVar x))), h1)
*)

  (***** all typing rules that use special let-bindings should be above *****)

  | ELet(x,Some(a),e1,e2) -> begin
      let ruleName = "TS-Let-Ann" in
      Wf.frame (spr "%s: let %s = ..." ruleName x) g a;
      Zzz.pushScope ();
      let (s1,h1) = applyFrame h a in
      tcExp g h (s1,h1) e1;
      Zzz.popScope ();
      let (n,g1) = tcAddBinding g h1 x s1 in
      let (s2,h2) = tsExp g1 h1 e2 in
(*
      tcRemoveBinding ();
*)
      tcRemoveBindingN n;
      finishLet (spr "%s: let %s = ..." ruleName x) g x [(x,s1)] (s2,h2)
(*
      let ruleName = "TS-Let" in
      let strE = spr "  let %s :: ... = ..." x in
      let (h0,(s1,h1)) = applyAnnotation g h a in
      tcExp g h (s1,h1) e1;
      (* TODO check annotation a *)
      Wf.wfScmFail (spr "ts ann ELet [%s] annotation" x) g h s1;
      let h1 = h0 @ h1 in
      let (g,h1) = tcAddBinding g h1 x s1 in
      (* 9/23 added snapshot
         TODO might want to add bindings to the env without pushing their
         types, since they're already there? *)
      let (n,g) = snapshot g h1 in
      let (s2,h2) = tsExp g h1 e2 in
      tcRemoveBindingN n;
      tcRemoveBinding ();
      finishLet [ruleName; strE] g x [(x,s1)] (s2,h2)
*)
    end

  | ELet(x,None,e1,e2) -> begin
      let ruleName = "TS-Let-Bare" in
      Zzz.pushScope ();
      let (s1,h1) = tsExp g h e1 in
      Zzz.popScope ();
      let (n,g1) = tcAddBinding g h1 x s1 in
      let (s2,h2) = tsExp g1 h1 e2 in
(*
      tcRemoveBinding ();
*)
      tcRemoveBindingN n;
      finishLet (spr "%s: let %s = ..." ruleName x) g x [(x,s1)] (s2,h2)
(*
      let ruleName = "TS-Let-Bare" in
      let (s1,h1) = tsExp g h e1 in
      let (g,h1) = tcAddBinding g h1 x s1 in
      (* 9/23 added snapshot
         TODO might want to add bindings to the env without pushing their
         types, since they're already there? *)
      let (n,g) = snapshot g h1 in
      let (s2,h2) = tsExp g h1 e2 in
      tcRemoveBindingN n;
      tcRemoveBinding ();
      finishLet [ruleName; spr "  let %s = ..." x] g x [(x,s1)] (s2,h2)
*)
    end

  | EIf(EVal(v),e1,e2) -> begin 
      tcVal g h tyBool v;
      Zzz.pushForm (pGuard v true);
      let (s1,h1) = tsExp g h e1 in (* same g, since no new bindings *)
      Zzz.popForm ();
      Zzz.pushForm (pGuard v false);
      let (s2,h2) = tsExp g h e2 in (* same g, since no new bindings *)
      Zzz.popForm ();
      (* TODO better join for heaps *)
      let h12 = Sub.simpleHeapJoin v h1 h2 in
      let x = freshVar "_ret_if" in
      let p =
        pAnd [pImp (pGuard v true) (applyTyp s1 (wVar x));
              pImp (pGuard v false) (applyTyp s2 (wVar x))]
      in
      (TRefinement(x,p), h12)
    end

  | EExtern(x,s,e) -> begin
      if !depth > 0 then err [spr "extern [%s] not at top-level" x];
      Wf.typ (spr "ts extern %s" x) g h s;
      let (n,g) = tcAddBinding g h x s in
      let s2 = tsExp g h e in
(*
      tcRemoveBinding ();
*)
      tcRemoveBindingN n;
      s2
    end

  | EHeap(h,e) -> begin
      if !depth <> 0  then failwith "ts EHeap: should be at top-level";
      if !initHeapSet then failwith "ts EHeap: init heap already set!";
      Wf.heap "EHeap: initial heap" g h;
      initHeapSet := true;
      let (n,g) = snapshot g h in 
      let (s,h') = tsExp g h e in
      tcRemoveBindingN n;
      (s, h')
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
      let w = applyFrame h f in
      tcExp g h w (EAsW(s,e,w));
      w
    end

  | EAsW(s,e,w) -> begin
      Wf.world (spr "TS-EAsW: %s" s) g w;
      tcExp g h w e;
      w
    end

  | ELabel(x,ao,e) -> begin
      failwith "ts elabel"
(*
      let ruleName = "TS-Label" in
      let strE = spr "  #%s { ... }" x in
      Zzz.pushScope ();
      let a =
        match ao with
          | None -> failwith "TS-Label no annotation"
          | Some(a) -> a in
      let (h0,(s1,h1)) = applyAnnotation g h a in
      let w = tsExp (Label(x,Some(s1,h1))::g) h e in
      Zzz.popScope ();
      niceCheckWorlds [ruleName; strE] g w (s1,h1);
      (s1, h0 @ h1)
      (* TODO make sure this case is okay *)
*)
    end

  (* TODO 9/25 revisit *)
  | EBreak(x,EVal(v)) -> begin
      let cap = spr "TS-Break: break %s (%s)" x (prettyStrVal v) in
      let lblBinding =
        try List.find (function Lbl(y,_) -> x = y | _ -> false) g
        with Not_found -> err [cap; "label not found"]
      in
      match lblBinding with
        | Lbl(_,Some(tGoal,hGoal)) -> begin
            tcVal g h tGoal v;
            ignore (Sub.heaps cap g h hGoal);
            (tyFls, botHeap)
          end
        | _ -> err [cap; "no goal for label"]
(*
      let ruleName = "TS-Break" in
      let strE = spr "  break %s (%s)" x (prettyStrVal v) in
      let (s1,h1) =
        match lookupLabel x g with
          | Some(Some(w)) -> w
          | Some(None)    -> niceError [ruleName; strE; "env has no world"]
          | None          -> niceError [ruleName; strE; "label not found"]
      in
      tcVal g h s1 v;
      ignore (niceCheckHeaps ["TS-Break"; strE] g h h1);
      (STyp tyFls, botHeap)
*)
    end

  | EThrow(EVal(v)) ->
      let _ = tsVal g h v in (tyFls, h)

  | ETryCatch _ -> failwith "ETryCatch"

  | ETryFinally _ -> failwith "ETryFinally"

  | ENewObj _ -> failwith "ts ENewObj: should've been typed with a let binding"

  | ELoadedSrc(_,e) -> tsExp g h e
  | ELoadSrc(s,_) ->
      failwith (spr "ts ELoadSrc [%s]: should've been expanded" s)

  (* the remaining cases should not make it to type checking, so they indicate
     some failure of parsing or ANFing *)

  | EBase _    -> Anf.badAnf "ts EBase"
  | EVar _     -> Anf.badAnf "ts EVar"
  | EDict _    -> Anf.badAnf "ts EDict"
  | EFun _     -> Anf.badAnf "ts EFun"
  | EIf _      -> Anf.badAnf "ts EIf"
  | EApp _     -> Anf.badAnf "ts EApp"
  | ENewref _  -> Anf.badAnf "ts ENewref"
(* TODO 11/29: falling back on special rule
  | ENewref(l,EVal(v)) ->
      let x = freshVar "dummylet" in
      tsExp g h (ELet(x,None,ENewref(l,EVal(v)),eVar x))
*)
  | EDeref _   -> Anf.badAnf "ts EDeref"
  | ESetref _  -> Anf.badAnf "ts ESetref"
  | EBreak _   -> Anf.badAnf "ts EBreak"
  | EThrow _   -> Anf.badAnf "ts EThrow"

and tsELetAppTryBoxes cap g curHeap x (tActs,lActs,hActs) v2 e boxes =

  let checkLength s l1 l2 =
    let (n1,n2) = (List.length l1, List.length l2) in
    if n1 <> n2 then err [cap; spr "expected %d %s args but got %d" n1 s n2] in

  let tryOne ((tForms,lForms,hForms),y,t11,e11,t12,e12) =

(*
    (* infer missing poly arg *)
    let hActs =
      match maybeInferHeapParam cap curHeap hActs hForms e11 with
        | Some(e) -> [e]
        | None    -> hActs in

    (* check well-formedness of all poly args *)
    checkLength "type" tForms tActs;
    checkLength "loc" lForms lActs;
    checkLength "heap" hForms hActs;
    (match Utils.someDupe lActs with
       | None    -> ()
       | Some(l) -> err [cap; spr "duplicate loc arg: %s" (strLoc l)]
    );
    let polySubst =
      ([], List.combine tForms tActs,
       List.combine lForms lActs, List.combine hForms hActs) in

    (* instantiate input world with poly args, and check that it's satisfied *)
    let (t11,e11) =
      (masterSubstTyp polySubst t11, masterSubstHeap polySubst e11) in
    let (t11,e11) =
      (expandPreTyp t11, expandPreHeap e11) in
    Wf.heap "e11 after instantiation" g e11;
    let binderVSubst = Sub.heaps cap g curHeap e11 in
    let t11 = masterSubstTyp (binderVSubst, [], [], []) t11 in
    tcVal g curHeap t11 v2;
*)

    (* check well-formedness of all poly args *)
    checkLength "type" tForms tActs;
    checkLength "loc" lForms lActs;
    (match Utils.someDupe lActs with
       | None    -> ()
       | Some(l) -> err [cap; spr "duplicate loc arg: %s" (strLoc l)]
    );
    let tSubst = List.combine tForms tActs in
    let lSubst = List.combine lForms lActs in

    (* instantiate input world with poly args *)
    let (t11,e11) =
      (masterSubstTyp ([],tSubst,lSubst,[]) t11,
       masterSubstHeap ([],tSubst,lSubst,[]) e11) in

    (* infer missing poly arg.
       note: this must take place after loc args have been substituted. *)
    let hActs =
      match maybeInferHeapParam cap curHeap hActs hForms e11 with
        | Some(e) -> [e]
        | None    -> hActs in

    (* TODO: hInst should really keep track of polarity. but for
       simplicity, just substituting the actual actual for all
       occurrences in the input heap, and substituting the selfified
       actual for all occurrences in the output heap *)

    checkLength "heap" hForms hActs;
    let hSubst = List.combine hForms hActs in

    (* instantiate input world with rest of poly args.
       expand from pre-formulas to formulas. check that the result is wf *)
    let (t11,e11) =
      (masterSubstTyp ([],[],[],hSubst) t11,
       masterSubstHeap ([],[],[],hSubst) e11) in
    let (t11,e11) =
      (expandPreTyp t11, expandPreHeap e11) in

(*
    Wf.heap "e11 after instantiation" g e11;
    let vSubst = Sub.heaps cap g curHeap e11 in
    let t11 = masterSubstTyp (vSubst,[],[],[]) t11 in
    tcVal g curHeap t11 v2;
*)
    let argSubst = (y, WVal v2) :: (depTupleSubst t11 (WVal v2)) in
    let e11 = masterSubstHeap (argSubst,[],[],[]) e11 in

    (* TODO 11/30: moved heapPreSubst here, since it also needs to be
       applied to input heap *)
    let heapPreSubst = (heapDepTupleSubst e11,[],[],[]) in
    let e11 = masterSubstHeap heapPreSubst e11 in

    Wf.heap "e11 after instantiation" g e11;
    let heapSubst = Sub.heaps cap g curHeap e11 in
    tcVal g curHeap t11 v2;

    (* TODO: see the note about hInst above *)

    let (freshFromHInst,hAct) =
      match hActs with
        | [e] -> selfifyHeap e
        | []  -> ([], ([],[]))
        | _   -> failwith "app: >1 heap arg nyi"
    in
    let hSubst = List.combine hForms [hAct] in

    let (nFromHInst,g) =
      List.fold_left (fun (n,g) (x,t) ->
        (* TODO is e11 the right one to pass in? *)
        let (m,g) = tcAddBinding g e11 x t in
        (n+m, g)
      ) (0,g) freshFromHInst in

    (* instantiate output world with poly args and binder substitution *)
    let polySubst = ([],tSubst,lSubst,hSubst) in
(*
    let heapPreSubst = (heapDepTupleSubst e11,[],[],[]) in
*)
    let valueSubst = (argSubst @ heapSubst,[],[],[]) in
(*
    let (fresh,(t12,e12)) =
      freshenWorld (t12,e12) in
*)
    let (t12,e12) =
      (masterSubstTyp polySubst t12, masterSubstHeap polySubst e12) in
    let (t12,e12) =
      (masterSubstTyp heapPreSubst t12, masterSubstHeap heapPreSubst e12) in
    let (t12,e12) =
      (masterSubstTyp valueSubst t12, masterSubstHeap valueSubst e12) in
    (* need to freshen after the argument heap binders have been substituted
       into return world *)
    let (fresh,(t12,e12)) =
      freshenWorld (t12,e12) in
    let (t12,e12) =
      (expandPreTyp t12, expandPreHeap e12) in
    Wf.heap "e12 after instantiation" g e12;

    (* now that call has been checked, process the let body *)
    let (n,g') = snapshot g e12 in
    let (m,g') = tcAddBinding g' e12 x t12 in
    let outWorld = tsExp g' e12 e in
(*
    tcRemoveBinding ();
    tcRemoveBindingN n;
*)
    tcRemoveBindingN (n + m);
    tcRemoveBindingN nFromHInst;
(*
    AppOk (fresh @ [(x,t12)], outWorld)
*)
    AppOk (freshFromHInst @ fresh @ [(x,t12)], outWorld)
  in
(*
  let ruleName = "TS-LetApp" in
  let tryOne (lf,y,t11,h11,t12,h12) =
    let subst = checkLocActuals ruleName lf la in
    let t11' = applyLocSubstTyp subst t11 in
    let t12' = applyLocSubstTyp subst t12 in
    let h11' = applyLocSubstHeap subst h11 in
    let h12' = applyLocSubstHeap subst h12 in
    let (h1,h2) = splitHeapForCall h h11' in
    Wf.wfHeapFail (spr "%s: split h1" ruleName) g h1;
    Wf.wfHeapFail (spr "%s: split h2" ruleName) g h2;
    let subst = Sub.checkHeapsFail ruleName g h2 h11' in
    (* tcVal g h (STyp (applyVarSubstTyp subst t11')) v2; *)
    tcVal g h2 (STyp (applyVarSubstTyp subst t11')) v2;
    let t = substTyp (AVal v2) (aVar y) (applyVarSubstTyp subst t12') in
    let (fresh,h2') = freshen (applyVarSubstHeap subst h12') in
    let h' = h1 @ h2' in
    let (n,g) = snapshot g h2' in
    let (g,h') = tcAddBinding g h' x (STyp t) in
    let (s3,h3) = tsExp g h' e in
    tcRemoveBinding ();
    tcRemoveBindingN n;
    AppOk (fresh @ [(x,STyp t)], (s3, h3))
  in
*)
  let result =
    (* use the first arrow that type checks the call *)
    Utils.fold_left_i (fun acc u i ->
      let s = prettyStrTT u in
      match acc, u with
        | AppOk _, _ -> acc
        | AppFail(l), UArr(uarr) -> begin
            try tryOne uarr
            with Tc_error(errList) ->
              AppFail (l @ [spr "\n*** box %d: %s" i s] @ errList)
          end
        | AppFail(l), _ -> AppFail (l @ [spr "box %d isn't an arrow: %s" i s])
    ) (AppFail []) boxes
  in
  match result with
    | AppOk(toElim,world) -> finishLet cap g x toElim world
    | AppFail(errors) ->
        let n = List.length boxes in
        let s = spr "%d boxes but none type check the call" n in
        printTcErr (cap :: s :: errors)
        (* the buck stops here, instead of raising Tc_error, since otherwise
           get lots of cascading let-bindings *)


(***** Value type conversion **************************************************)

and tcVal_ g h goal = function

  | (VBase _ as v)
  | (VVar _ as v)
  | (VEmpty as v)
  | (VExtend _ as v) ->
      let s = tsVal g h v in
      Sub.types (spr "TC-EVal: %s" (prettyStr strValue v)) g s goal

  | VFun(l,x,anno,e) ->
      let s = match anno with None -> "TC-Fun-Bare" | _ -> "TC-Fun-Ann" in
      tcVFun s g goal (l,x,anno,e)

and tcVFun ruleName g goal (l,x,anno,e) =
  let g = removeLabels g in
  let checkOne (((ts,ls,hs),y,t1,h1,t2,h2) as arr) =
    let u = UArr arr in
    Wf.typeTerm (spr "%s: arrow:\n  %s" ruleName (prettyStrTT u)) g ([],[]) u;
    let (ts,ls,hs) =
(* TODO requring all missing params now, since don't want to deal with
   heap prefix vars that get inserted...
      if l = ([],[],[]) then (ts,ls,hs) (* fill in omitted loc params *)
      else if l = (ts,ls,hs) then l
      else err [spr "%s: supplied poly params not equal to expected" ruleName]
*)
      if l = ([],[],[]) then (ts,ls,hs)
      else err ["lambda has some params..."]
    in
    let subst = ([(y, wVar x)], [], [], []) in
    let t2 = masterSubstTyp subst t2 in
    let h2 = masterSubstHeap subst h2 in
    let g = List.fold_left (fun acc x -> TVar(x)::acc) g ts in
    let g = List.fold_left (fun acc x -> LVar(x)::acc) g ls in
    let g = List.fold_left (fun acc x -> HVar(x)::acc) g hs in
    Zzz.pushScope ();
(*
    let (n,g) = snapshot g h1 in
    let (m,g) = tcAddBinding g h1 x t1 in
*)
    (* since input heap can refer to arg binders, need to process t1 first *)
    let (m,g) = tcAddBinding g h1 x t1 in
    let (n,g) = snapshot g h1 in
    (match anno with
       | None -> ()
       | Some(t,h) -> failwith "tc fun ann"
    );
    tcExp g h1 (t2,h2) e;
(*
    tcRemoveBinding ();
    tcRemoveBindingN n;
*)
    tcRemoveBindingN (n + m);
    Zzz.popScope ()
  in
(*
    Wf.wfLocFormalsFail ruleName l;
    let t2 = substVarInTyp x y t2 in
    let h1 = applyVarSubstHeap [x,y] h1 in
    let h2 = applyVarSubstHeap [x,y] h2 in
    Zzz.pushScope ();
    let (n,g) = snapshot g h1 in 
    let (g,h1) = tcAddBinding g h1 x (STyp t1) in
    (match anno with
       | None -> ()
       | Some(t,h) -> begin
           Wf.wfTypFail ruleName g h t;
           Wf.wfHeapFail ruleName g h1;
           Sub.checkTypes ruleName g TypeTerms.empty t1 t;
           ignore (Sub.checkHeapsFail ruleName g h1 h);
         end
    );
    tcExp g h1 (STyp t2, h2) e;
    tcRemoveBinding ();
    tcRemoveBindingN n;
    Zzz.popScope ();
  in 
*)
  match isArrows goal with 
    | Some(l) -> List.iter checkOne l
    | None    -> err [spr "%s: goal should be one or more arrows\n  %s"
                        ruleName (prettyStrTyp goal)]


(***** Expression type conversion *********************************************)

and tcExp_ g h goal = function

  | EVal(v) -> begin
      let (sGoal,hGoal) = goal in
      tcVal g h sGoal v;
      ignore (Sub.heaps (spr "TC-Val: %s" (prettyStrVal v)) g h hGoal)
    end

  | ELet(x,None,ENewref(l,EVal(v)),e) -> begin
(*
      failwith (spr "Tc elet newref goal: %s" (strWorld goal))
*)
      let cap = spr "TC-LetNewref-Bare: let %s = ..." x in
      let e = EAsW (cap, e, goal) in
      let w = tsExp g h (ELet(x,None,ENewref(l,EVal(v)),e)) in
      ignore (Sub.worlds cap g w goal)
(*
      let ruleName = "TC-LetNewref" in
      let strE = spr "  let %s = ref %s (%s) in ..." x l (prettyStrVal v) in
      let e = wrapWithGoal ruleName x e w in
      let w' = tsExp g h (ELet(x,None,ENewref(l,EVal(v)),e)) in
      niceCheckWorlds [ruleName; strE; strW] g w' w
*)
    end

  | EDeref(EVal(v)) -> begin
(*
      failwith "Tc deref"
*)
      let w = tsExp g h (EDeref(EVal(v))) in
      let cap = spr "TC-Deref: !(%s)" (prettyStrVal v) in
      ignore (Sub.worlds cap g w goal)
(*
      let ruleName = "TC-Deref" in
      let strE = spr "  !(%s)" (prettyStrVal v) in
      let w' = tsExp g h (EDeref(EVal(v))) in
      niceCheckWorlds [ruleName; strE; strW] g w' w
*)
    end

(*
  TODO 9/27 why was this case needed?
  | ELet(x,Some(a0),EDeref(EVal(v)),e) -> begin
      let ruleName = "TC-LetDeref" in
      let strE = spr "  let %s :: ... = !(%s) in ..." x (prettyStrVal v) in
      let e = wrapWithGoal ruleName x e a in
      let (s,h') = tsExp g h (ELet(x,Some(a0),EDeref(EVal(v)),e)) in
      let (s0,sGoal) = (scmOfAnn a0, scmOfAnn a) in     
      niceCheckSchemes [ruleName; strE; spr "checking s < s0"] g s s0;
      niceCheckSchemes [ruleName; strE; spr "checking s0 < goal"] g s0 sGoal;
      finishHeap [ruleName; strE] g h' a
    end
*)

  | ELet(x,None,ESetref(EVal(v1),EVal(v2)),e) -> begin
(*
      failwith (spr "Tc let setref: goal world:\n\n%s" (strWorld goal))
*)
      let cap = spr "TC-LetSetref-Bare: let %s = ..." x in
      let e = EAsW (cap, e, goal) in
      let w = tsExp g h (ELet(x,None,ESetref(EVal(v1),EVal(v2)),e)) in
      ignore (Sub.worlds cap g w goal)
(*
      let ruleName = "TC-LetSetref" in
      let strE = spr "  let %s = (%s) := (%s) in ..." x
                    (prettyStrVal v1) (prettyStrVal v2) in
      let e = wrapWithGoal ruleName x e w in
      let w' = tsExp g h (ELet(x,None,ESetref(EVal(v1),EVal(v2)),e)) in
      niceCheckWorlds [ruleName; strE; strW] g w' w
*)
    end

(*
  | EFreeze _ -> failwith "tc EFreeze"
*)

  | ELet(x,None,EApp(l,EVal(v1),EVal(v2)),e) -> begin
(*
      (* TODO wrap with goal *)
*)
      let (s1,s2) = (prettyStrVal v1, prettyStrVal v2) in
      let cap = spr "TC-LetApp: let %s = [...] (%s) (%s)" x s1 s2 in
      let e = EAsW (cap, e, goal) in
      let w = tsExp g h (ELet(x,None,EApp(l,EVal(v1),EVal(v2)),e)) in
      ignore (Sub.worlds cap g w goal)
(*
      (* TODO hmm, how to help the application, not just the body *)
      let ruleName = "TC-LetApp" in
      let strE = spr "  let %s = (%s) <%s> (%s) in ..."
                   x (prettyStrVal v1) (strLocs la) (prettyStrVal v2) in
      let e = wrapWithGoal ruleName x e w in
      let w' = tsExp g h (ELet(x,None,EApp(EVal(v1),la,EVal(v2)),e)) in
      niceCheckWorlds [ruleName; strE; strW] g w' w
*)
    end

  (* 9/21: special case added when trying to handle ANFed ifs *)
  (* 11/25: added this back in *)
  | ELet(x,None,e1,EVal(VVar(x'))) when x = x' -> begin
(*
      failwith "tc let special"
*)
      tcExp g h goal e1;
      (* adding binding just so the type is printed *)
      let (n,_) = tcAddBinding g (snd goal) x (fst goal) in
      tcRemoveBindingN n;
(*
      let ruleName = "TC-Let special" in
      let strE = spr "  let %s = ... in %s" x x in
      tcExp g h w e1;
      (* adding binding just so the type is printed *)
      ignore (tcAddBinding g (snd w) x (fst w));
      tcRemoveBinding ();
*)
    end

  | ELet(x,None,ENewObj(l1,l2,EVal(v)),e) -> begin
      let cap = spr "TC-NewObj: let %s = ..." x in
      let e = EAsW (cap, e, goal) in
      let w = tsExp g h (ELet(x,None,ENewObj(l1,l2,EVal(v)),e)) in
      ignore (Sub.worlds cap g w goal)
    end

  (***** all typing rules that use special let-bindings should be above *****)

  | ELet(x,None,e1,e2) -> begin
      (* TODO wrap with goal *)
(*
      let e2 = wrapWithGoal (spr "TC-Let: let %s = ..." x) e2 goal
*)

(* TODO post 11/25 *)
      let cap = spr "TC-Let: let %s = ..." x in
      let e2 = EAsW (cap, e2, goal) in
      let w = tsExp g h (ELet(x,None,e1,e2)) in
      ignore (Sub.worlds cap g w goal)

(* pre 11/25
      let w = tsExp g h (ELet(x,None,e1,e2)) in
      ignore (Sub.worlds (spr "TC-Let-Bare: let %s = ..." x) g w goal)
*)


(*
      let ruleName = "TC-Let" in
      let strE = spr "  let %s = ..." x in
      let e2 = wrapWithGoal ruleName x e2 w in
      let w' = tsExp g h (ELet(x,None,e1,e2)) in
      niceCheckWorlds [ruleName; strE; strW] g w' w
*)
    end

  | ELet(x,Some(a1),e1,e2) -> begin
      let ruleName = "TC-Let-Ann" in
      Wf.frame (spr "%s: let %s = ..." ruleName x) g a1;
      Zzz.pushScope ();
      let (s1,h1) = applyFrame h a1 in
      tcExp g h (s1,h1) e1;
      Zzz.popScope ();
      let (n,g1) = tcAddBinding g h1 x s1 in
      tcExp g h1 goal e2;
      tcRemoveBindingN n;
(*
      let ruleName = "TC-Let" in
      let strE = spr "  let %s = ..." x in
      let (h0,(s1,h1)) = applyAnnotation g h a1 in
      (* TODO change to wf annotation *)
      Wf.wfScmFail ruleName g h s1;
      Zzz.pushScope ();
      tcExp g h (s1,h1) e1;
      Zzz.popScope ();
      let h1 = h0 @ h1 in
      let (g,h1) = tcAddBinding g h1 x s1 in
      (* 9/23 added snapshot
         TODO might want to add bindings to the env without pushing their
         types, since they're already there? *)
      let (n,g) = snapshot g h1 in
      tcExp g h1 w e2;
      tcRemoveBindingN n;
      tcRemoveBinding ();
*)
    end

  | EIf(EVal(v),e1,e2) -> begin
      tcVal g h tyBool v;
      Zzz.pushForm (pGuard v true);
      tcExp g h goal e1;  (* same g, since no new bindings *)
      Zzz.popForm ();
      Zzz.pushForm (pGuard v false);
      tcExp g h goal e2; (* same g, since no new bindings *)
      Zzz.popForm ();
    end

  | EHeap(h,e) -> failwith "tc EHeap"

  | EExtern _ -> failwith "tc EExtern"

  | ETcFail(s,e) ->
      let fail =
        try let _ = tcExp g h goal e in false
        with Tc_error _ -> true in
      if fail
        then ()
        else err [spr "tc ETcFail: [\"%s\"] should have failed" s]

  | EAs(_,e,f) -> begin
      let w = applyFrame h f in
      tcExp g h w e;
      ignore (Sub.worlds "TC-EAs" g w goal)
    end

  | EAsW(_,e,w) -> begin
      tcExp g h w e;
      ignore (Sub.worlds "TC-EAsW" g w goal)
    end

  | ELabel(x,ao,e) -> begin
      tcExp (Lbl(x,Some(goal))::g) h goal e
(*
      (* TODO 9/28 completely ignoring the annotation. is this okay? *)
      tcExp (Label(x,Some(w))::g) h w e
*)
    end

  | EBreak(x,EVal(v)) -> begin
      let w = tsExp g h (EBreak(x,EVal(v))) in
      let cap = (spr "TC-Break: %s" x) in
      ignore (Sub.worlds cap g w goal)
    end

  | EThrow _ -> failwith "tc EThrow"
  | ETryCatch _ -> failwith "tc ETryCatch"
  | ETryFinally _ -> failwith "tc ETryFinally"

  (* 11/26: going through a let-binding, since that's the only
     synthesis rule for new obj *)
  | ENewObj(l1,l2,EVal(v)) -> begin
      (* failwith "tc ENewObj: should've been checked with let-binding" *)

      let x = freshVar "_tc_newobj" in
      let w = tsExp g h (ELet(x,None,ENewObj(l1,l2,EVal(v)),eVar(x))) in
      let cap = spr "TC-NewObj: %s %s" (strLoc l1) (strLoc l2) in
      ignore (Sub.worlds cap g w goal)
(*
      failwith (spr "tc newobj, goal:\n%sj" (strWorld goal))
*)
    end

  (* the remaining cases should not make it to type checking, so they indicate
     some failure of parsing or ANFing *)

  | EBase _    -> Anf.badAnf "tc EBase"
  | EVar _     -> Anf.badAnf "tc EVar"
  | EDict _    -> Anf.badAnf "tc EDict"
  | EFun _     -> Anf.badAnf "tc EFun"
  | EIf _      -> Anf.badAnf "tc EIf"
  | EApp _     -> Anf.badAnf "tc EApp"
  | ENewref _  -> Anf.badAnf "tc ENewref"
  | EDeref _   -> Anf.badAnf "tc EDeref"
  | ESetref _  -> Anf.badAnf "tc ESetref"


(***** Entry point ************************************************************)

let typecheck e =
  let g = [] in
  let (_,g) = tcAddBinding ~printHeap:false g ([],[]) "v" tyAny in
  let (_,g) = tcAddBinding ~printHeap:false g ([],[]) "dObject" tyEmpty in
  (* TODO *)
  let (_,g) =
    tcAddBinding ~printHeap:false g ([],[]) "__Object" (tyRef lObject) in
  let h = ([], [(lObject, HConcObj ("dObject", tyAny, lRoot))]) in
  try begin
    ignore (tsExp g h e);
    let s = spr "OK! %d queries." !Zzz.queryCount in
    pr "\n%s\n" (Utils.greenString s)
  end with Tc_error(s) ->
    printTcErr s

