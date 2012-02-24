
(***** "functional arrays" ****************************************************)

val length :: [A] a:Arr(A) -> {Int | (implies (packed a) (= v (len a)))}

val geti :: [A] a:Arr(A) -> i:{Int|(>= v 0)} ->
  {(ite (packed a)
        (ite (< i (len a)) (and (v::A) (= v (sel a i))) (= v undefined))
        (or (v::A) (= v undefined)))}

val seti :: [A] a:Arr(A) -> i:{Int|(>= v 0)} -> x:A ->
  {(and (v::Arr(A))
        (= (sel a i) x)
        (ite (and (packed a) (< i (len a)))
             (and (packed v) (= (len v) (len a))) true)
        (ite (and (packed a) (= i (len a)))
             (and (packed v) (= (len v) (+ 1 (len a)))) true))}

val push :: [A] a:Arr(A) -> x:A ->
  {(and (v::Arr(A)) 
        (implies (packed a) (and (packed v)
                                 (= (len v) (+ 1 (len a)))
                                 (= (sel a (len a)) x))))}

val top :: [A] a:Arr(A) -> {(ite (packed a)
                                 (and (v::A) (= v (sel a (- (len a) 1))))
                                 (or (v::A) (= v undefined)))}

(*
val pop :: [A] a:Arr(A) ->
  [_:Int,
   _:{(and (v::Arr(A)) )}]
*)

(*
  didn't fail means packed(a) => len(a) > 0
*)

