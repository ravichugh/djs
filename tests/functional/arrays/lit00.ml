
#use "tests/functional/arrays/__arrays.ml"

let tup0 = <> in
let tup1 = <1> in
let tup2 = <1, True> in

let _ :: {(and (v :: Arr(Top)) (packed v) (= (len v) 0))} = tup0 in
let _ :: {(and (v :: Arr(Top)) (packed v) (= (len v) 1))} = tup1 in
let _ :: {(and (v :: Arr(Top)) (packed v) (= (len v) 2))} = tup2 in

let _ :: {(= v 1)} = ([Top] geti) tup1 0 in
let _ :: {(= v 1)} = ([Top] geti) tup2 0 in
let _ :: {(= v True)} = ([Top] geti) tup2 1 in

let tup3 = ([Top] push) tup2 "hi" in

let _ :: {(and (v :: Arr(Top)) (packed v) (= (len v) 3))} = tup3 in

0
