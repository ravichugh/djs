
#use "tests/functional/arrays/__arrays.ml"

val tup3 :: {(and (v::Arr({(not (= v undefined))}))
                  (packed v) (= (len v) 3)
                  (Int (sel v 0))
                  (Bool (sel v 1))
                  (Str (sel v 2)))}

let tup2 = ([{(not (= v undefined))}] pop) tup3 in

let _ :: {(= (len tup2) 2)} = 0 in

let _ :: {(= v undefined)} = ([{(not (= v undefined))}] geti) tup2 2 in

let _ :: {(not (= v undefined))} = ([{(not (= v undefined))}] geti) tup2 1 in

0
