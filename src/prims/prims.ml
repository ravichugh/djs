

(***** System D tag-test ******************************************************)

(* val tagof :: x:Top -> {(= v (tag x))} *)


(***** System D dictionary operations *****************************************)

val mem :: d:Dict -> k:Str -> {Bool|(iff (= v true) (has d {k}))}

val get :: d:Dict -> k:{Str|(has d {v})} -> {(= v (sel d k))}

val set :: d:Dict -> k:Str -> z:Top -> {(= v (upd d k z))}

val del :: d:Dict -> k:Str -> {(= v (upd d k bot))}


(***** JS primitives **********************************************************)

val js_plus :: x:{(or (= (tag v) "number") (= (tag v) "string"))}
            -> y:{(= (tag v) (tag x))}
            -> {(and (= (tag v) (tag x))
                     (implies (= (tag x) "number") (= v (+ x y))))}

val js_uminus :: x:Int -> Int

val js_or :: x:Top -> y:Top -> {(ite (falsy x) (= v y) (= v x))}

val js_and :: x:Top -> y:Top -> {(ite (truthy x) (= v y) (= v x))}

val js_not :: x:Top -> {Bool|(iff (= v true) (falsy x))}

val js_eek :: (* == *)
  x:Top -> y:Top -> {Bool|(implies (= (tag x) (tag y)) (= x y))}

val js_threek :: (* === *)
  x:Top -> y:{(= (tag v) (tag x))} -> {Bool|(iff (= v true) (= x y))}

val js_lt :: x:Int -> y:Int -> {Bool|(iff (= v true) (< x y))}
val js_le :: x:Int -> y:Int -> {Bool|(iff (= v true) (<= x y))}
val js_gt :: x:Int -> y:Int -> {Bool|(iff (= v true) (> x y))}
val js_ge :: x:Int -> y:Int -> {Bool|(iff (= v true) (>= x y))}


(***** recursion **************************************************************)

(* val fix :: [A] x:(y:A->A) -> A *)


(******************************************************************************)

let end_of_prims :: Int = 0

