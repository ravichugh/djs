
#use "tests/functional/arrays/__arrays.ml"

val tup2 :: {(and (v::Arr(Int)) (packed v) (= (len v) 2)
                  (= (sel v 0) 0)
                  (= (sel v 1) 1))}

let _ :: {(= v 2)} = ([Int] length) tup2 in
let _ :: {(= v 0)} = ([Int] geti) tup2 0 in
let _ :: {(= v 1)} = ([Int] geti) tup2 1 in
let _ :: {(= v undefined)} = ([Int] geti) tup2 2 in

0
