
open Lang
open LangUtils


let checkConversion = ref true

type clause = formula * formula list

let oc_cnf = open_out "out/cnf.lisp"

(* can set flag to true to output each step of translation *)
let debugForm f =
  if false then fpr oc_cnf "--\n\n %s\n\n" (prettyStrForm f);
  f


(***** CNF ********************************************************************)

(*
let map f = mapForm false f (fun x -> x) (fun x -> x)
*)

let rec map f = function
  | PConn(s,ps) -> f (PConn (s, List.map (map f) ps))
  | p           -> f p

let removeIff =
  map (function
    | PConn("iff",[p;q]) -> pAnd [pImp p q; pImp q p]
    | p                  -> p)

let removeImp =
  map (function
    | PConn("implies",[p;q]) -> pOr [pNot p; q]
    | f                      -> f)

let pushNotsDown =
  map (function
    | PConn("not",[PConn("and",l)]) -> pOr (List.map (fun p -> pNot p) l)
    | PConn("not",[PConn("or",l)])  -> pAnd (List.map (fun p -> pNot p) l)
    | f                             -> f)

let removeDoubleNots =
  map (function
    | PConn("not",[PConn("not",[f])]) -> f
    | f                               -> f)

let rec toCnfLists f =
  match f with
    | PTru | PFls | PEq _ | PApp _
    | PUn _ | PHeapHas _
    | PHas _ | PDomEq _ | PEqMod _ | PObjHas _ -> [[f]]
    | PConn("not",_) -> [[f]]
    | PConn("and",l) -> List.concat (List.map toCnfLists l)
    | PConn("or",l)  -> let l' = List.map toCnfLists l in
                        let tuples = Utils.cartesianProduct l' in
                        List.map List.concat tuples
    | PConn(s,_)     -> failwith (spr "toCnfLists: PConn [%s]" s)
    | PAll _         -> failwith "toCnfLists: PAll shouldn't appear"

let checkCnfLists l =
  let rec isAtomic = function
    | PTru | PFls | PEq _ | PApp _         -> true
    | PUn _ | PHas _ | PDomEq _ | PEqMod _ -> true
    | PHeapHas _ | PObjHas _               -> true
    | PConn("and",_) | PConn("or",_)       -> false
    | PConn("implies",_) | PConn("iff",_)  -> false
    | PConn("not",[PConn("not",_)])        -> false
    | PConn("not",[p])                     -> isAtomic p
    | PConn(s,_)     -> failwith (spr "isAtomic: PConn [%s]" s)
    | PAll _         -> failwith "toCnfLists: PAll shouldn't appear"
  in
  if List.for_all (List.for_all isAtomic) l then l
  else failwith "checkCnfLists; see cnf.lisp"

let liftClauseList l =
  pAnd (List.map (fun (p,qs) ->
    pImp p (pOr (List.map (fun q -> PUn q) qs))) l)


(***** Normalize **************************************************************)

let normalizeCnfClauses l =
  List.map (fun clause ->
(*
    let (l1,rhs) =
      List.partition (function PIs _ -> false | _ -> true) clause in
    let lhs = PAnd (List.map (fun p -> PNot p) l1) in
    (lhs, rhs)
*)
    let (lhs,rhs) =
      List.fold_left
        (fun (l,r) -> function PUn(q) -> (l, q::r) | p -> ((pNot p)::l, r))
        ([],[]) (List.rev clause) in
    (pAnd lhs, rhs)
  ) l

let convert f =
  let l =
    f |> removeIff         (* |> debugForm *)
      |> removeImp         (* |> debugForm *)
      |> pushNotsDown      (* |> debugForm *)
      |> removeDoubleNots  (* |> debugForm *)
      |> toCnfLists
      |> Utils.removeDupes
      |> checkCnfLists
      |> normalizeCnfClauses
  in
  if !checkConversion then begin
    let f' = liftClauseList l in
    fpr oc_cnf "*****\n\n %s\n\n to cnf \n\n %s\n\n"
      (prettyStrForm f) (prettyStrForm f');
    if not (Zzz.checkValid "cnf conversion" (pIff f f')) then
      kill "bad cnf conversion; see cnf.lisp\n"
  end;
  l

