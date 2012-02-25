
(***** "functional arrays" ****************************************************)

(* TODO add finite-foralls for seti, push, and pop *)

val length :: [A] a:Arr(A) -> {Int | (implies (packed a) (= v (len a)))}

val geti :: [A] a:Arr(A) -> i:Int ->
  {(ite (and (packed a) (>= i 0))
        (ite (< i (len a)) (and (v::A) (= v (sel a i))) (= v undefined))
        (or (v::A) (= v undefined)))}

val seti :: [A] a:Arr(A) -> i:Int -> x:A ->
  {(and (v::Arr(A))
        (= (sel a i) x)
        (implies (and (packed a) (>= i 0) (< i (len a)))
                 (and (packed v) (= (len v) (len a))))
        (implies (and (packed a) (= i (len a)))
                 (and (packed v) (= (len v) (+ 1 (len a))))))}

val push :: [A] a:Arr(A) -> x:A ->
  {(and (v::Arr(A)) 
        (implies (packed a) (and (packed v)
                                 (= (len v) (+ 1 (len a)))
                                 (= (sel a (len a)) x))))}

val top :: [A] a:Arr(A) ->
  {(ite (packed a)
        (and (v::A) (= v (sel a (- (len a) 1))))
        (or (v::A) (= v undefined)))}

val pop :: [A] a:Arr(A) ->
  {(and (v::Arr(A))
        (implies (packed a)
                 (and (packed v) (= (len v) (- (len a) 1)) (> (len a) 0))))}

