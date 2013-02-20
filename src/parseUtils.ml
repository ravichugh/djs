
open Lang
open LangUtils

module S = Settings

let useTuplesAndPats = true


(***** Command-line options ***************************************************)

let argSpecs = [
  ("-parseOnly", Arg.Set S.parseOnly, "");
  ("-augmentHeaps", Arg.Bool (fun b -> S.augmentHeaps := b),
                 "   <bool> infer some omitted heap bindings (default=true)");
  ("-strictWarn", Arg.Bool (fun b -> S.strictWarn := b),
               "     <bool> treat warnings as errors (default=true)");
  ("-checkCNF", Arg.Set Cnf.checkConversion,
             "       check CNF conversion");
  ("-fast", Arg.Unit (fun () ->
              Cnf.checkConversion := false;
              Log.printToStdout := false;
              Log.printToLog := false;
              S.checkWfSynthesis := false;
              ()),
         "           suppress output; forgo CNF and other sanity checks");
  ("-printAllTypes", Arg.Set S.printAllTypes,
                  "  otherwise just print top-level definitions");
  ("-eagerFlush", Arg.Set Log.eagerFlush,
               "     eagerly flush to out/log.txt and stdout, helpful for debugging");
  ("-tryAllBoxes", Arg.Set S.tryAllBoxesHack,
                "    try all boxes, in case typeTerms misses some");
  ("-timeout", Arg.Int (fun i -> S.zzzTimeout := i),
            "        <int> Z3 timeout in ms; 0 means none (default=0)");
  ("-doFalseChecks", Arg.Set S.doFalseChecks,
                  "  do false checks (de-optimization)");
  ("-noQuickTypes", Arg.Clear S.quickTypes,
                 "   do all subtyping with logical queries (de-optimization)");
  ("-booleanGuards", Arg.Set S.booleanGuards,
                  "  require boolean guards to conditionals");
  ("-exactJoins", Arg.Set S.exactJoins,
               "     compute exact joins even when a variable is annotated");
]


(*

(***** Tuple type desugaring **************************************************)

let fld i = wStr (string_of_int i)

let mkTupleTyp typs =
  let n = List.length typs in
  (* if n <= 1 then parse_err "mkTupleTyp: need at least one"; *)
  let v = freshVar "tuple" in
  let av = wVar v in
  let has = PHas (av, List.map fld (Utils.list0N (pred n))) in
  let sels =
    (* TODO handle other typs or make this a rawtyp ? *)
    Utils.mapi (fun (TRefinement(x,p)) i ->
      substForm (sel av (fld i)) (wVar x) p
    ) typs
  in
  TRefinement (v, pAnd (PEq (tag av, wStr "Dict") :: has :: sels))

let mkDepTupleSubst tup vars =
  Utils.mapi (fun x i -> (wVar x, sel (wVar tup) (fld i))) vars

let mkDepTupleTyp l =
  let n = List.length l in
  (* if n <= 1 then parse_err "mkTupleTyp: need at least one"; *)
  let y = freshVar "depTuple" in
  let ay = wVar y in
  let subst = mkDepTupleSubst y (List.map fst l) in
  let has = PHas (ay, List.map fld (Utils.list0N (pred n))) in
  let sels =
    Utils.mapi (fun (TRefinement(x,p)) i ->
      p |> substForm (sel ay (fld i)) (wVar x) |> applySubstForm subst
    ) (List.map snd l)
  in
  TRefinement (y, pAnd (PEq (tag ay, wStr "Dict") :: has :: sels))

let mkDepTupleArrow (vars,t1) (h1,t2,h2) =
  let x = freshVar "depTupleFormal" in
  let subst = mkDepTupleSubst x vars in
  let h1 = applySubstHeap subst h1 in
  let t2 = applySubstTyp subst t2 in
  let h2 = applySubstHeap subst h2 in
  (x, t1, h1, t2, h2)

*)

(***** Tuple expression desugaring ********************************************)

let mkTupleExp exps =
  if useTuplesAndPats then ETuple exps
  else EDict (Utils.map_i (fun e i -> (EVal (vStr (string_of_int i)), e)) exps)


(***** Pattern desugaring *****************************************************)

let rec addLets e = function
  | [] -> e
  | (x,e1)::tl -> ELet (x, None, e1, addLets e tl)

(* below are four different functions that convert a pattern into
   intermediate let-bindings. each successive version does a better job. *)

(*

let patternToBindings1 initBinder pat =
  let rec expOfAtom = function
    | AVal(VVar(x)) -> EVal (VVar x)
    | AVal(VBase(Str(s))) -> EVal (VBase (Str s))
    | ATwo(FSel,a1,a2) -> mkApp (eVar "get") [expOfAtom a1; expOfAtom a2]
    | a -> failwith (spr "expOfAtom [%s]: should not happen" (strAtom a)) in
  let rec foo curPath = function
    | PLeaf(x) -> [(x, expOfAtom curPath)]
    | PNode(l) ->
        List.concat
          (Utils.mapi
             (fun pat i -> foo (sel curPath (fld i)) pat) l)
  in
  foo (wVar initBinder) pat

let patternToBindings2 initBinder pat =
  let rec foo curVar = function
    | PLeaf(x) -> [(x, eVar curVar)]
    | PNode(l) ->
        List.concat
          (Utils.mapi (fun pat i ->
            let si = string_of_int i in
            let newVar = freshVar "pattern" in
            let newExp = mkApp (eVar "get") [eVar curVar; EVal (vStr si)] in
            (newVar, newExp) :: (foo newVar pat)
          ) l)
  in
  foo initBinder pat

(* this version prevents an extra binding for PLeaf patterns *)
let patternToBindings3 initBinder pat =
  let rec foo curVar = function
    | PLeaf(x) -> failwith "ParseUtils: shouldn't get here"
    | PNode(l) ->
        List.concat
          (Utils.mapi (fun pat i ->
             let si = string_of_int i in
             let newExp = mkApp (eVar "get") [eVar curVar; EVal (vStr si)] in
             match pat with
               | PLeaf(x) -> [(x, newExp)]
               | _ -> let newVar = freshVar "pattern" in
                      (newVar, newExp) :: (foo newVar pat)
          ) l)
  in
  foo initBinder pat

*)

(* this version applies "get" only once on each PNode pattern *)
let patternToBindings4 initBinder pat =
  let rec foo curVarGet = function
    | PLeaf(x) -> failwith "ParseUtils: shouldn't get here"
    | PNode(l) ->
        List.concat
          (Utils.map_i (fun pat i ->
             let si = string_of_int i in
             let newExp = mkApp (eVar curVarGet) [EVal (vStr si)] in
             match pat with
               | PLeaf(x) -> [(x, newExp)]
               | _ -> let newVar = freshVar "pattern" in
                      (newVar, mkApp (eVar "get_curried") [newExp]) :: (foo newVar pat)
          ) l)
  in
  let newVar = freshVar "pattern" in
  (newVar, mkApp (eVar "get_curried") [eVar initBinder]) :: (foo newVar pat)

let mkPatFun pat e =
  if useTuplesAndPats then vFun (pat, e)
  else
    let initBinder = freshVar "pattern" in
    let newBindings = patternToBindings4 initBinder pat in
    let e' = addLets e newBindings in
    vFun (PLeaf initBinder, e')


(***** Misc *******************************************************************)

let maybeAddHeapPrefixVar : uarrow -> uarrow = function
  | ((ts,ls,[]),x,t,([],cs1),t2,([],cs2)) ->
      let h = freshHVar () in
      ((ts,ls,[h]), x, t, ([h],cs1), t2, ([h],cs2))
  | arr -> arr

let typToFrame t =
  let h = freshHVar () in
  ([h], ([h],[]), (t,([h],[])))

(*

(***** Recursive function desugaring ******************************************)

let stripTypeVars e s =
  let rec foo vars = function
    | ETFun(x,e), SAll(x',s) when x = x' -> foo (x::vars) (e,s)
    | _, SAll _  -> None
    | inner_e, STyp(t) -> Some (List.rev vars, inner_e, t)
  in foo [] (e,s)

(*  given    val f :: all l. x:t1/h2 -> t2/h2
      and    letrec f x = e1 in e2

   create    let f :: all l. x:t1/h2 -> t2/h2 =
               fix [all l.x:t1/h2 -> t2/h2]
                 (fun (f: (all l.x:t1/h2 -> t2/h2)) / [] -> 
                    fun <l...> (x: t1) / h1 ->
                      let tmprec :: t2 = e1 in
                      tmprec)
             in e2
*)
let mkLetRecMono f (l,x,t1,h1,t2,h2) e1 e2 =
  let t = tRefinement (PIs (theV, UArr (l, x, t1, h1, t2, h2))) in
  ELet (f, Some (AScm (STyp t)),
        mkApp (ETApp (eVar "fix", t))
          [EFun ([], f, Some (t, []), (* TODO dangerous: using same f! *)
             EFun (l, x, Some (t1, h1),
                   (* EAs ("mkLetRecMono checkRetType", e1, STyp t2, Some h2)))], *)
(* TODO 9/27 equality pred for same frame?
                   EAs ("mkLetRecMono checkRetType", e1,
                        AFrame (h2, (STyp t2, h2)))))],
*)
                   e1))],
                   (* ELet (tmp, Some (STyp t2), Some h2, e1, eVar tmp)))], *)
        e2)

let rec mkLetRec f s e1 e2 =
  match e1, s with
    (* ignoring type annotation on lambda *)
    | EFun(_,x,_,e), STyp(TRefinement("v",PIs(a,UArr(l,y,t1,h1,t2,h2)))) ->
      begin
        if a <> theV then parse_err "mkLetRec: not v";
        (* 9/21 allowing different binders *)
        let t2 = substVarInTyp x y t2 in
        let h1 = substVarInHeap x y h1 in
        let h2 = substVarInHeap x y h2 in
        mkLetRecMono f (l,x,t1,h1,t2,h2) e e2
      end
    | ETFun _, SAll _ -> begin
        match stripTypeVars e1 s with
          | None -> parse_err "mkLetRec: type lams and foralls don't match up"
          | Some(l,inner_e,t) ->
              let mono_f = f in (* TODO dangerous: using same f! *)
              let inner_e = substVarInExp mono_f f inner_e in 
              let mono_rec_def =
                mkLetRec mono_f (STyp t) inner_e (eVar mono_f) in
              ELet (f, Some (AScm s), mkTypeFuns l mono_rec_def, e2)
      end
    | EFun _, STyp _ ->
        parse_err (spr "mkLetRec: term lambda but polytype \n\n%s"
          (prettyStr strScm s))
    | _ ->
        parse_err "mkLetRec: ?"
*)



(*  given    val f :: [A;L;H] x:t1/e1 -> t2/e2
      and    letrec f x = e1 in e2

   create    let f :: [A;L;H] x:t1/e1 -> t2/e2 =
                fix [ [A;L;H] x:t1/e1 -> t2/e2 ] (fun f x -> e)
             in e2
*)
let mkLetRec f uarr e1 e2 =
  let (_,x,_,_,_,_) = uarr in
  let t = tyTypTerm (UArrow uarr) in
  ELet (f, Some (typToFrame t),
        EApp (([t],[],[]), eVar "fix", eFun (PLeaf f, eFun (PLeaf x, e1))),
        e2)

(* like the previous version, but without the extra annotation
     let f = fix [U] (fun f x -> e) in e2
*)
let mkLetRec_ f uarr e1 e2 =
  let (_,x,_,_,_,_) = uarr in
  let t = tyTypTerm (UArrow uarr) in
  ELet (f, None,
        EApp (([t],[],[]), eVar "fix", eFun (PLeaf f, eFun (PLeaf x, e1))),
        e2)


(***** Hack for Primitive Intersections ***************************************)

let doIntersectionHack x = pNot (PEq (wStr "type hack", wStr x))

let undoIntersectionHack g t =
  let fForm = function
    | PConn("not",[PEq(WVal({value=VBase(Str("type hack"))}),
                       WVal({value=VBase(Str(x))}))]) ->
      begin
        try begin
          match List.find (function Var(y,_) -> x = y | _ -> false) g with
            | Var(_,s) ->
                (match s with
                   | TQuick("v",QBoxes([u]),p) when p = pTru -> PHasTyp (theV, u)
                   | _ -> Log.printTcErr [spr "0 can't expand type hack [%s]" x])
            | _ -> kill "undoIntersectionHack: impossible"
        end with Not_found ->
          Log.printTcErr [spr "1 can't expand type hack [%s]" x]
      end
    | p -> p
  in
  let t = mapTyp ~fForm t in
  match t with
    | TRefinement("v",PConn("and",ps)) ->
        let boxes_opt =
          List.fold_left (fun acc p ->
            match acc, p with
              | Some(l), PHasTyp(WVal({value=VVar"v"}),u) -> Some(u::l)
              | _ -> None
          ) (Some []) ps in
        begin match boxes_opt with
          | Some([]) -> tyAny
          | Some(us) -> TQuick ("v", QBoxes us, pTru)
          | None -> t
        end
    | _ ->
        t

