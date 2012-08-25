
open Lang
open LangUtils


(***** A-Normalization ********************************************************)

(* - insert EVals in all places where the type system requires a value,
     by adding let bindings for all intermediate operations.
   - if desired, could do a little more work to check when creating a
     temporary is unnecessary because the rhs is already a value.
 *)

let freshTmp () = freshVar "_"

let rec mkExp (l,ebody) =
  match l with
    | (x,ao,e)::l' -> ELet (x, ao, e, mkExp (l',ebody))
    | []           -> ebody

(* 11/29: revamped ANF *)

let maybeTmp = function
  | EVal(v) -> ([], EVal v)
  | e       -> let z = freshTmp () in
               ([z,None,e], eVar z)

(* adding additional let bindings to satisfy what tc expects *)
(* TODO remove this once tc uses existentials everywhere *)
let finish (l,e) =
  let b = match e with
            | EApp _ | ENewref _ | ESetref _ -> true
            | _ -> false in
  if b
  then let z = freshTmp () in (l @ [z,None,e], eVar z)
  else (l, e)

let rec anf = function
  | EVal(w) -> ([], EVal w)
  | EFun(l,x,t,e) -> ([], EVal (wrapVal pos0 (VFun (l, x, t, anfExp e))))
  | EDict(xel) ->
      let (ll,xwl) =
        xel |> List.map (fun (e1,e2) ->
                 let (l1,e1) = anfAndTmp e1 in
                 let (l2,e2) = anfAndTmp e2 in
                 (match e1, e2 with
                    | EVal(w1),EVal(w2) -> (l1@l2, (w1,w2))
                    | _  -> failwith "anf: expr in dict not value?"))
            |> List.split
      in
      let vdict =
        List.fold_left
          (fun acc (w1,w2) -> wrapVal pos0 (VExtend (acc, w1, w2)))
          (wrapVal pos0 VEmpty) xwl
      in
      finish (List.concat ll, EVal vdict)
(* TODO want to use this version, but the special let rule in TcDref
   currently requires the version below.
  | EIf(e1,e2,e3) ->
      let (l1,e1) = anfAndTmp e1 in
      finish (l1, EIf (e1, anfExp e2, anfExp e3))
*)
  | EArray(t,el) ->
      let (ll,vl) = el |> List.map anfAndTmp |> List.split in
      let vl =
        List.map
          (function EVal(v) -> v | _ -> failwith "anf: expr in arr?") vl in
      finish (List.concat ll, EVal ({pos=pos0; value=VArray (t, vl)}))
  | ETuple(el) ->
      let (ll,vl) = el |> List.map anfAndTmp |> List.split in
      let vl =
        List.map
          (function EVal(v) -> v | _ -> failwith "anf: expr in tuple?") vl in
      finish (List.concat ll, EVal ({pos=pos0; value=VTuple vl}))
  | EIf(e1,e2,e3) ->
      let (l1,e1') = anf e1 in
      let z1 = freshTmp () in
      let z23 = freshTmp () in
      let l' = [(z1, None, e1');
                (z23, None, EIf (eVar z1, anfExp e2, anfExp e3))] in
      (l1 @ l', eVar z23)
  | EApp(appargs,e1,e2) ->
      let (l1,e1) = anfAndTmp e1 in
      let (l2,e2) = anfAndTmp e2 in
      finish (l1 @ l2, EApp (appargs, e1, e2))
  | ELet(x,ao,e1,e2) ->
      if true then (* 8/14: set this back to true *)
        (* original and 11/1 version: maintains same lexical scoping *)
        ([], ELet (x, ao, anfExp e1, anfExp e2))
      else if true then
        (* 9/6 version: flattens scoping TODO need to avoid clashes *)
        let (l1,e1) = anf e1 in
        let (l2,e2) = anf e2 in
        (l1 @ [x, ao, e1] @ l2, e2)
      else
        (* pre 9/6 version: flattens equation scope TODO need to avoid clashes *)
        let (l1,e1) = anf e1 in
        (l1, ELet (x, ao, e1, anfExp e2))
  | EExtern(x,s,e) -> ([], EExtern (x, s, anfExp e))
  | ETcFail(s,e) -> ([], ETcFail (s, anfExp e))
  | EAs(x,e,a) -> ([], EAs (x, anfExp e, a))
  | EAsW(x,e,a) -> ([], EAsW (x, anfExp e, a))
  | ENewref(cl,e) ->
      let (l,e) = anfAndTmp e in
      finish (l, ENewref (cl, e))
  | EDeref(e) ->
      let (l,e) = anfAndTmp e in
      finish (l, EDeref e)
  | ESetref(e1,e2) ->
      let (l1,e1) = anfAndTmp e1 in
      let (l2,e2) = anfAndTmp e2 in
      finish (l1 @ l2, ESetref (e1, e2))
  | EWeak(h,e) -> ([], EWeak (h, anfExp e))
  | ELabel(x,e) -> ([], ELabel (x, anfExp e))
  | EBreak(x,e) ->
      let (l,e) = anfAndTmp e in
      (l, EBreak (x, e))
  | ETryCatch(e1,x,e2) -> ([], ETryCatch (anfExp e1, x, anfExp e2))
  | ETryFinally(e1,e2) -> ([], ETryFinally (anfExp e1, anfExp e2))
  | EThrow(e) ->
      let (l,e) = anfAndTmp e in
      finish (l, EThrow e)
  | ENewObj(e1,loc1,e2,loc2) ->
      let (l1,e1) = anfAndTmp e1 in
      let (l2,e2) = anfAndTmp e2 in
      finish (l1 @ l2, ENewObj (e1, loc1, e2, loc2))
  | ELoadedSrc(s,e) -> ([], ELoadedSrc (s, anfExp e))
  | EFreeze(loc,x,e) ->
      let (l,e) = anfAndTmp e in
      finish (l, EFreeze (loc, x, e))
  | EThaw(loc,e) ->
      let (l,e) = anfAndTmp e in
      finish (l, EThaw (loc, e))

and anfAndTmp e =
  let (l1,e) = anf e in
  let (l2,e) = maybeTmp e in
  (l1 @ l2, e)

and anfExp e = mkExp (anf e)

(* Clean up the results of ANFing a bit.
     let _tmp = e1 in
     let y = _tmp in     
       e2
*)
let removeUselessLet = function
(*
  | ELet(x,None,e1,ELet(y,None,EVal(VVar(x')),e2)) when x = x' && x.[0] = '_' ->
*)
  | ELet(x,None,e1,ELet(y,None,EVal({value=VVar(x')}),e2))
    when x = x' && x.[0] = '_' ->
      ELet (y, None, e1, e2)
  | e -> e

let anfExp e = e |> anfExp |> mapExp removeUselessLet


(***** A-Normalized program printer *******************************************)

(* The return value of strVal and strExp is expected to be aligned at the
   nesting level k. The caller can clip any leading whitespace if it wants
   to include the first line of the return value on the current line.
*)

let badAnf s = failwith (spr "[%s] ANFer did something wrong here" s)

let noLineBreaks s = not (String.contains s '\n')

let clip = Utils.clip

let tab k = String.make (2 * k) ' '

let rec strVal_ k = function
  | VVar(x) -> spr "%s%s" (tab k) x
(*
  | VFun([],x,None,e) when !Settings.langMode = Settings.D -> strLam k x e
  | VFun([],x,Some(t,[]),e) when !Settings.langMode = Settings.D ->
      strLam k (spr "(%s)" (strBindingTyp (x,t))) e
*)
  (* 11/28: to avoid parsing conflict, function values wrapped in begin/end *)
  | VFun(l,x,None,e) ->
      let s = strLamImp k l x e in
      spr "%sbegin %s end" (tab k) (clip s)
  | VFun(l,x,Some(t,h),e) ->
      let s = strLamImp k l (spr "(%s) / %s" (strBinding (x,t)) (strHeap h)) e in
      spr "%sbegin %s end" (tab k) (clip s)
  | VNull -> spr "%snull" (tab k)
  | VBase(c) -> spr "%s%s" (tab k) (strBaseValue c)
  (* | VEmpty -> spr "%s{}" (tab k) *)
  | VEmpty -> spr "%sempty" (tab k)
  | VExtend(v1,v2,v3) ->
      let s1 = strVal k v1 in
      let s2 = strVal k v2 in
      let s3 = strVal k v3 in
      (* spr "%s(upd %s %s %s)" (tab k) (clip s1) (clip s2) (clip s3) *)
      spr "%s(%s with %s = %s)" (tab k) (clip s1) (clip s2) (clip s3)
(*
  | VExtend(w1,w2,w3) ->
      (* since no concrete syntax for record extension, using calls to set *)
      let x1 = freshVar "tmp" in
      let x2 = freshVar "tmp" in
      let x3 = freshVar "tmp" in
      let y1 = freshVar "vextend1" in
      let y2 = freshVar "vextend2" in
      let y3 = freshVar "vextend3" in
      strExp k (ELet (y1, None, EVal w1,
                ELet (y2, None, EVal w2,
                ELet (y3, None, EVal w3,
                ELet (x1, None, mkApp (eVar "set") [eVar y1],
                ELet (x2, None, mkApp (eVar x1) [eVar y2],
                ELet (x3, None, mkApp (eVar x2) [eVar y3],
                  eVar x3)))))))
*)
  | VArray(t,vs) ->
      let st = if t = tyArrDefault then "" else spr " as Arr(%s)" (strTyp t) in
      (* let st = spr " as %s" (strTyp t) in *)
      let svs = List.map (fun s -> clip (strVal k s)) vs in
      spr "%s<%s>%s" (tab k) (String.concat ", " svs) st 
  | VTuple(vs) ->
      let svs = List.map (fun s -> clip (strVal k s)) vs in
      spr "%s(%s)" (tab k) (String.concat ", " svs)

and strVal k v = strVal_ k v.value

(*
and strLam k sarg e =
  let sexp = strExp (succ k) e in
  if noLineBreaks sexp
    then spr "%sfun %s -> %s" (tab k) sarg (clip sexp)
    else spr "%sfun %s -> \n%s" (tab k) sarg sexp
*)

and strLamImp k (l1,l2,l3) sarg e =
  let sexp = strExp (succ k) e in
(*
  let sl =
    if List.length l = 0 then ""
    else spr "<%s> " (strLocs l) in
*)
  let sl =
    if List.length l1 + List.length l2 + List.length l3 = 0 then ""
    else spr "[%s;%s;%s] " (String.concat "," l1)
           (String.concat "," l2) (String.concat "," l3) in
(*
  if noLineBreaks sexp
    then spr "%sfun %s%s -> %s" (tab k) sl sarg (clip sexp)
    else spr "%sfun %s%s -> \n%s" (tab k) sl sarg sexp
*)
  if noLineBreaks sexp
    then spr "%sfun %s%s -> (%s)" (tab k) sl sarg (clip sexp)
    else spr "%sfun %s%s -> (\n%s\n%s)" (tab k) sl sarg sexp (tab k)

and strBam k x e =
  let se = strExp (succ k) e in
  if noLineBreaks se
    then spr "%sfun %s -> %s" (tab k) x (clip se)
    else spr "%sfun %s -> \n%s" (tab k) x se

(* TODO for better formatting, should always check for newlines before clipping *)
and strExp k exp = match exp with
  | EVal(w) -> strVal k w
  | EIf(EVal(w1),e2,e3) ->
      spr "%sif %s then \n%s\n%selse \n%s"
        (tab k) (clip (strVal k w1))
          (strExp (succ k) e2)
        (tab k)
          (strExp (succ k) e3)
  | EApp(([],[],[]),EVal(w1),EVal(w2)) ->
      let s1 = strVal k w1 in
      let s2 = strVal k w2 in
      spr "%s %s(%s)" (tab k) (clip s1) (clip s2)
  | EApp((ts,ls,hs),EVal(w1),EVal(w2)) ->
      let s1 = strVal k w1 in
      let s2 = strVal k w2 in
      let s0 = spr "[ %s; %s; %s ]" (* first space in particular to avoid [[ *)
                 (String.concat "," (List.map strTyp ts))
                 (strLocs ls)
                 (String.concat "," (List.map strHeap hs)) in
      spr "%s(%s %s)(%s)" (tab k) s0 (clip s1) (clip s2)
(*
        if ls = [] then ""
        else spr "<%s> " (strLocs ls) in
      spr "%s%s %s(%s)" (tab k) (clip s1) sl (clip s2)
*)
  | ELet(x,ao,e1,e2) ->
(*
      (* TODO remove these and use abstract syntax for separators *)
      let sep =
        if x = "end_of_prims" ||
           x = "end_of_pervasives" ||
           x = "end_of_djs_prelude" then
          spr "\n\n(%s)\n\n" (String.make 78 '*')
        else if k = 0 then "\n\n"
        else "\n"
      in
*)
      let sep = if k = 0 then "\n\n" else "\n" in
      let sao =
        match ao with
          | None -> ""
          | Some([x],h1,(t2,h2)) when h1 = ([x],[]) && h1 = h2 ->
              spr " :: %s" (strTyp t2)
          | Some(a) -> spr " ::: %s" (strFrame a)
      in
      let s1 = strExp (succ k) e1 in
      let s2 = strExp k e2 in
      if noLineBreaks s1
        then spr "%slet %s%s = %s in%s%s" (tab k) x sao (clip s1) sep s2
        else spr "%slet %s%s =\n%s in%s%s" (tab k) x sao s1 sep s2
  (* TODO For Extern, Assert, and Assume, print str_ in flat mode *)
  | EExtern(x,s,e) ->
      spr "%sval %s :: %s\n\n%s" (tab k) x (clip (strTyp s)) (strExp k e)
  | ETcFail(s,e) ->
      spr "%s(fail \"%s\" \n%s)" (tab k) s (strExp (succ k) e)
  | EAs(_,e,f) ->
      let sf = strFrame f in
      spr "%s(%s\n%s) as %s" (tab k) (clip (strExp k e)) (tab k) sf
  | EAsW(_,e,w) ->
      let sw = strWorld w in
      spr "%s(%s\n%s) as %s" (tab k) (clip (strExp k e)) (tab k) sw
  | ENewref(x,e) ->
      spr "%sref %s %s" (tab k) (strLoc x) (clip (strExp k e))
  | EDeref(e) -> spr "%s(!%s)" (tab k) (clip (strExp k e))
  (* TODO split lines? *)
  | ESetref(e1,e2) ->
      let s1 = strExp k e1 in
      let s2 = strExp k e2 in
      spr "%s%s := %s" (tab k) (clip s1) (clip s2)
  | EWeak(h,e) -> spr "%sweak %s\n\n%s" (tab k) (strWeakLoc h) (strExp k e)
  | ELabel(x,e) ->
      let se = strExp (succ k) e in
      spr "%s#%s {\n%s\n%s}" (tab k) x se (tab k)
  | EBreak(x,e) ->
      let s = strExp (succ k) e in
      spr "%sbreak #%s %s" (tab k) x (clip s)
  | EThrow(e) ->
      let s = strExp (succ k) e in
      spr "%sthrow %s" (tab k) (clip s)
  (* TODO put block on single line if short enough *)
  | ETryCatch(e1,x,e2) ->
      let (s1,s2) = strExp (succ k) e1, strExp (succ k) e2 in
      spr "%stry {\n%s\n%s} catch (%s) {\n%s\n%s}" (tab k) s1 (tab k) x s2 (tab k)
  | ETryFinally(e1,e2) ->
      let (s1,s2) = strExp (succ k) e1, strExp (succ k) e2 in
      spr "%stry {\n%s\n%s} finally {\n%s\n%s}" (tab k) s1 (tab k) s2 (tab k)
  | ENewObj(EVal(v1),l1,EVal(v2),l2) ->
      let s1 = strVal (succ k) v1 in
      let s2 = strVal (succ k) v2 in
      spr "%snew (%s, %s, %s, %s)"
        (tab k) (clip s1) (strLoc l1) (clip s2) (strLoc l2)
  | EFreeze(l,x,EVal(v)) ->
      let sx = strThawState x in
      spr "%sfreeze (%s, %s, %s)" (tab k) (strLoc l) sx (clip (strVal (succ k) v))
  | EThaw(l,EVal(v)) ->
      spr "%sthaw (%s, %s)" (tab k) (strLoc l) (clip (strVal (succ k) v))
  | EFun _         -> badAnf "EFun"
  | EDict _        -> badAnf "EDict"
  | EIf _          -> badAnf "EIf"
  | EApp _         -> badAnf "EApp"
  | ENewObj _      -> badAnf "ENewObj"
  | EFreeze _      -> badAnf "EFreeze"
  | EThaw _        -> badAnf "EThaw"
  | ELoadedSrc(s,e) ->
      let s = Str.replace_first (Str.regexp Settings.djs_dir) "DJS_DIR/" s in
      let n = max 0 (70 - String.length s) in
      let sep = spr "(***** %s %s*)" s (String.make n '*') in
      spr "%s%s\n\n%s" (tab k) sep (strExp k e)

let printAnfExp e =
  let oc = open_out (Settings.out_dir ^ "anfExp.dref") in
  fpr oc "%s\n" (strExp 0 e);
  flush oc;
  ()


(***** Coercion from expression to ANF expression *****************************)

(* When a source file is processed "raw", it is expected to be in ANF.
   Instead of requiring the parser to check that the things that should be
   values are indeed values, allow the parser to be oblivious about raw
   mode; that is, allow it to produce E- versions of expressions everywhere.
   But then have the expression go through this coercion to ANF.
   Alternatively, could have a duplicate version of the parser that only
   accepts A-normal programs. *)

let rec coerceVal e =
  match coerce e with
    | EVal(w) -> w
    | _       -> failwith "coerceVal"

and coerceEVal from e =
  match coerce e with
    | EVal(w) -> EVal w
    | _       -> failwith (spr "coerceEVal: called from %s" from)

and coerce = function
  | EVal(w) -> EVal w
  | EDict([]) -> EVal (wrapVal pos0 VEmpty)
  | EDict _ -> failwith "Anf.coerce EDict: should have become calls to set"
  | EFun(l,x,t,e) -> EVal (wrapVal pos0 (VFun (l, x, t, coerce e)))
  | EArray(t,es) -> EVal (wrapVal pos0 (VArray (t, List.map coerceVal es)))
  | EIf(e1,e2,e3) -> EIf (coerceEVal "if" e1, coerce e2, coerce e3)
  | EApp(l,e1,e2) -> EApp (l, coerceEVal "app1" e1, coerceEVal "app2" e2)
  | ELet(x,ao,e1,e2) -> ELet (x, ao, coerce e1, coerce e2)
  | EExtern(x,s,e) -> EExtern (x, s, coerce e)
  | ETcFail(s,e) -> ETcFail (s, coerce e)
  | EAs(x,e,a) -> EAs (x, coerce e, a)
  | ENewref(cl,e) -> ENewref (cl, coerce e)
  | EDeref(e) -> EDeref (coerceEVal "deref" e)
  | ESetref(e1,e2) -> ESetref (coerceEVal "setref1" e1, coerceEVal "setref2" e2)
  | EWeak(h,e) -> EWeak (h, coerce e)
  | ELabel(x,e) -> ELabel (x, coerce e)
  | EBreak(x,e) -> EBreak (x, coerceEVal "break" e)
  | EThrow(e) -> EThrow (coerceEVal "throw" e)
  | ETryCatch(e1,x,e2) -> ETryCatch (coerce e1, x, coerce e2)
  | ETryFinally(e1,e2) -> ETryFinally (coerce e1, coerce e2)
  | ENewObj(e1,l1,e2,l2) ->
      ENewObj (coerceEVal "NewObj" e1, l1, coerceEVal "NewObj" e2, l2)
  | ELoadSrc(s,e) -> ELoadSrc (s, coerce e)
  | ELoadedSrc(s,e) -> ELoadedSrc (s, coerce e)
  | EFreeze(l,x,e) -> EFreeze (l, x, coerceEVal "EFreeze" e)
  | EThaw(l,e) -> EThaw (l, coerceEVal "EThaw" e)

