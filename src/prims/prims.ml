

(***** run-time tag-test ******************************************************)

val tagof :: x:Top -> {(= v (tag x))}


(*
(***** untyped equality *******************************************************)

val eq :: x:Top -> y:Top -> {Bool|(iff (= v True) (= x y))}

*)

(*

(***** operations on base values **********************************************)

val plus :: x:Int -> y:Int -> {Int|(= v (+ x y))}
val minus :: x:Int -> y:Int -> {Int|(= v (- x y))}
val mult :: x:Int -> y:Int -> Int
val lt :: x:Int -> y:Int -> {Bool|(iff (= v True) (< x y))}
val le :: x:Int -> y:Int -> {Bool|(iff (= v True) (<= x y))}
val gt :: x:Int -> y:Int -> {Bool|(iff (= v True) (> x y))}
val ge :: x:Int -> y:Int -> {Bool|(iff (= v True) (>= x y))}

*)
val unary_minus :: x:Int -> Int

val neg :: b:Bool -> {Bool|(iff (= v True) (= b False))}
val l_and :: x:Bool -> y:Bool -> {(ite (= x True) (= v y) (= v False))}

(*
val l_or :: x:Bool -> y:Bool ->
  {(ite (or (= x True) (= y True)) (= v True) (= v False))}
(*
val l_and :: b0:Bool -> b1:Bool ->
                 {Bool | (and (implies (= b0 True) (= v b1))
                              (implies (= b0 False) (= v False)))}
val l_or :: b0:Bool -> b1:Bool ->
                {Bool | (iff (= v True) (or (= b0 True) (= b1 True)))}
*)

val strlen :: s:Str -> Int
val strcat :: s0:Str -> s1:Str -> Str
val strOfInt :: x:Int -> Str

*)


(***** System D dictionary operations *****************************************)

val mem :: d:Dict -> k:Str -> {Bool|(iff (= v True) (has d {k}))}

val get :: d:Dict -> k:{Str|(has d {v})} -> {(= v (sel d k))}

val set :: d:Dict -> k:Str -> z:Top -> {(= v (upd d k z))}

val del :: d:Dict -> k:Str -> {(= v (upd d k bot))}


(***** JS primitives **********************************************************)

val jsPlus :: x:{(or (= (tag v) "number") (= (tag v) "string"))}
           -> y:{(= (tag v) (tag x))}
           -> {(and (= (tag v) (tag x))
                    (implies (= (tag x) "number") (= v (+ x y))))}

val jsOr :: x:Top -> y:Top -> {(ite (falsy x) (= v y) (= v x))}

val jsAnd :: x:Top -> y:Top -> {(ite (truthy x) (= v y) (= v x))}

val jsNot :: x:Top -> {Bool|(iff (= v True) (falsy x))}

val jsEek :: (* == *)
  x:Top -> y:Top -> {Bool|(implies (= (tag x) (tag y)) (= x y))}

val jsThreek :: (* === *)
  x:Top -> y:{(= (tag v) (tag x))} -> {Bool|(iff (= v True) (= x y))}


(***** recursion **************************************************************)

(* don't need this in Dref... *)
val fix :: [A] x:(y:A->A) -> A


(***** lists ******************************************************************)

(* no datatypes in !D

type List[+A] {
  "hd" : A;
  "tl" : List[*A]
}

val keys :: x:Dict -> List[{(and (= (tag v) "Str") (has x v))}]
*)


(***** imperative, prototype-backed object operations *************************)

(*
val objHas :: [; L1,L2; H]
     _:[x:Ref(L1), y:Str] / [H ++ L1 |-> (d:Top, L2)]
  -> {Bool|(iff (= v True) ObjHas([d],y,H,L2))} / same

val objHasOwn :: [; L1,L2; H]
     _:[x:Ref(L1), y:Str] / [H ++ L1 |-> (d:Top, L2)]
  -> {Bool|(iff (= v True) (has d {y}))} / same

val objGet :: [; L1,L2; H]
     _:[x:Ref(L1), y:Str] / [H ++ L1 |-> (d:{ObjHas([v],y,H,L2)}, L2)]
  -> {(= v ObjSel([d],y,H,L2))} / same

val objSet :: [; L1,L2; H]
     _:[x:Ref(L1), y:Str, z:Top] / [H ++ L1 |-> (d:Top, L2)]
  -> {(= v z)} / [H ++ L1 |-> (d':{(= v (upd d y z))}, L2)]
*)


(******************************************************************************)

let end_of_prims :: Int = 0

