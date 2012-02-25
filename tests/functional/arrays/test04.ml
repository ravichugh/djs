
#use "tests/functional/arrays/arrays.ml"

val tup3 :: {(and (v::Arr({(not (= v undefined))}))
                  (packed v) (= (len v) 3)
                  ((sel v 0) : Int)
                  ((sel v 1) : Bool)
                  ((sel v 2) : Str))}

let tup2 = ([{(not (= v undefined))}] pop) tup3 in

let _ :: {(= (len tup2) 2)} = 0 in

let _ :: {(= v undefined)} = ([{(not (= v undefined))}] geti) tup2 2 in

let _ :: {(not (= v undefined))} = ([{(not (= v undefined))}] geti) tup2 1 in

0
