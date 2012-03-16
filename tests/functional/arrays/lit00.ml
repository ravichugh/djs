
#use "tests/functional/arrays/__arrays.ml"

let tup0 = <> in
let tup1 = <1> in
let tup2 = <1, true> in

let _ :: {(and (v :: Arr({(not (= v undefined))})) (packed v) (= (len v) 0))} = tup0 in
let _ :: {(and (v :: Arr({(not (= v undefined))})) (packed v) (= (len v) 1))} = tup1 in
let _ :: {(and (v :: Arr({(not (= v undefined))})) (packed v) (= (len v) 2))} = tup2 in

let _ :: {(= v 1)} = ([{(not (= v undefined))}] geti) tup1 0 in
let _ :: {(= v 1)} = ([{(not (= v undefined))}] geti) tup2 0 in
let _ :: {(= v true)} = ([{(not (= v undefined))}] geti) tup2 1 in

let tup3 = ([{(not (= v undefined))}] push) tup2 "hi" in

let _ :: {(and (v :: Arr({(not (= v undefined))})) (packed v) (= (len v) 3))} = tup3 in

0
