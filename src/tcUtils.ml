
open Lang
open LangUtils


(***** Local Variable Elimination *********************************************)

(* check if p is w = x or x = w for some w *)
let isEqPred x = function
  | PEq(w,WVal(VVar(x'))) when x = x' -> Some w
  | PEq(WVal(VVar(x')),w) when x = x' -> Some w
  | _                                 -> None

(* if t is of the form    { y:Bool | y=True <=> p } for some p
   and q is of the form   x = True (resp. False)
   then convert to        p (resp. not p)
*)
let elimBoolFlag x t q =
  match t with
    | TBaseRefine(y,"Bool",PConn("iff",[PEq(w1,w2);p]))
      when w1 = wVar y && w2 = wBool true -> begin
        match isEqPred x q with
          | Some(WVal(VBase(Bool b))) -> Some (if b then p else pNot p)
          | _ -> None
      end
    | _ -> None

(* if q is x = w, then convert to [[T]](w) *)
let elimSingleton x t q =
  match isEqPred x q with
    | Some(w) -> Some (applyTyp t w)
    | None    -> None

(* if q is of the form    d' = upd(d,k,x)
   then convert to        eqmod(d',d,{x}) /\ [[T]](sel(d',k))
*)
let elimUpd x t = function
  | PEq(d',WVal(VExtend(d,k,VVar(x')))) when x = x' ->
      Some (pAnd [eqmod d' (WVal d) [WVal k];
                  applyTyp t (sel d' (WVal k))])
  | PEq(d',WApp("upd",[d;k;x'])) when x' = wVar x ->
      Some (pAnd [eqmod d' d [k];
                  applyTyp t (sel d' k)])
  | _ -> None

(* // if t is of the form    {y:Dict|y=upd(d,k,z)}
   if t is of the form    {y|y=upd(d,k,z)}
   and q is of the form   d' = upd(x,k',z')
   then convert to        eqmod(d',d,{k})
                          /\ (k=k' => sel(d',k')=z')
                          /\ (k!=k' => sel(d',k)=z /\ sel(d',k')=z')
*)
let elimNestedUpd x t q =
  match t, q with
(*
    | TBaseRefine(y,"Dict",PEq(y',WVal(VExtend(d,k,z)))),
*)
    | TRefinement(y,PEq(y',WVal(VExtend(d,k,z)))),
      PEq(d',WVal(VExtend(VVar(x'),k',z'))) when y' = wVar y && x' = x ->
        Some (pAnd [eqmod d' (WVal d) [WVal k];
                    pImp (PEq (WVal k, WVal k'))
                         (PEq (sel d' (WVal k'), WVal z'));
                    pImp (pNot (PEq (WVal k, WVal k')))
                         (pAnd [PEq (sel d' (WVal k), WVal z);
                                PEq (sel d' (WVal k'), WVal z')]) ])
    | TRefinement(y,PEq(y',WApp("upd",[d;k;z]))),
      PEq(d',WApp("upd",[x';k';z'])) when y' = wVar y && x' = wVar x ->
        Some (pAnd [eqmod d' d [k];
                    pImp (PEq (k, k'))
                         (PEq (sel d' k', z'));
                    pImp (pNot (PEq (k, k')))
                         (pAnd [PEq (sel d' k, z);
                                PEq (sel d' k', z')]) ])
    | _ -> None

(* if q is of the form  eqmod(d',upd(d,k,x),Keys)
   then convert to      eqmod(d',d,Keys)       if k in Keys
                        eqmod(d',d,Keys+{k})
                          /\ [[T]](sel(d',k))  ow
*)
let elimEqModUpd x t = function
  | PEqMod(d',WVal(VExtend(d,k,VVar(x'))),keys) when x = x' ->
      if List.mem (WVal k) keys then
        failwith "elimEqModUpd"
      else
        Some (pAnd [PEqMod (d', WVal d, (WVal k)::keys);
                    applyTyp t (sel d' (WVal k))])
  | PEqMod(d',WApp("upd",[d;k;x']),keys) when x' = wVar x ->
      if List.mem k keys then
        failwith "elimEqModUpd"
      else
        Some (pAnd [PEqMod (d', d, k::keys);
                    applyTyp t (sel d' k)])
  | _ -> None

let rec tryAllElim x t q = function
  | []    -> None
  | f::fs -> (match f x t q with
                | Some(q') -> Some q'
                | None     -> tryAllElim x t q fs)

let allFormulaRules =
  [elimBoolFlag; elimUpd; elimNestedUpd; elimEqModUpd; elimSingleton]

(* if t = {y|y=w}, then replace occurrences of x with w *)
let elimLocalWalue x t q =
  match t with
    | TRefinement(y,p) ->
        begin match isEqPred y p with
          | Some(w) -> mapForm ~fWal:(fun w' -> if w' = wVar x then w else w') q
          | None -> q
        end
    | _ -> q

(* after trying to match all formula structures, punts to elimLocalWalue *)
let elimLocalForm x t q =
  let fForm q =
    match tryAllElim x t q allFormulaRules with
      | Some(q') -> q'
      | None -> q
  in
  let q = mapForm ~fForm q in
  let q = elimLocalWalue x t q in
  q

(* tries a single top-level elimination rule, then punts to elimLocalForm *)
let rec elimLocalTyp x t s =
  let fForm = elimLocalForm x t in
  match s with
    | TRefinement(z,q) ->
        begin match isEqPred x q with
          | Some(WVal(VVar(z'))) when z = z' -> t
          | _ -> mapTyp ~fForm s
        end
    | _ -> mapTyp ~fForm s

(** wrapped version that logs each call **)

let oc_elim = open_out (Settings.out_dir ^ "elim.txt")
let count_all = ref 0
let count_elim = ref 0

let elimLocalTyp x s1 s2 =
  let s2' = elimLocalTyp x s1 s2 in
  incr count_all;
  fpr oc_elim "%s\n\nelimLocalTyp (%d)\n\n%s :: %s\n\n%s\n\n"
    (String.make 80 '-') !count_all x
    (prettyStr strTyp s1) (prettyStr strTyp s2);
  if s2 <> s2' then begin
    incr count_elim;
    fpr oc_elim "%s eliminated:\n\n%s\n\n" x (prettyStr strTyp s2');
  end;
  s2'

let elimLocalHeap x t (hs,cs) =
  let cs =
    List.map (function
      | (l,HConc(y,s))       -> (l, HConc (y, elimLocalTyp x t s))
      | (l,HConcObj(y,s,l')) -> (l, HConcObj (y, elimLocalTyp x t s, l'))
    ) cs
  in
  (hs, cs)

