
#use "tests/functional/arrays/__arrays.ml"

val tup0 :: {(and (v::Arr(Int)) (packed v) (= (len v) 0))}

let _ :: {(= v 0)} = ([Int] length) tup0 in
let _ :: Top = ([Int] geti) tup0 0 in
let _ :: {(or (Int v) (= v undefined))} = ([Int] geti) tup0 0 in
let _ :: {(= v undefined)} = ([Int] geti) tup0 0 in

let tup1 = ([Int] push) tup0 0 in
let _ :: {(= v 1)} = ([Int] length) tup1 in

let tup2 = ([Int] push) tup1 1 in
let _ :: {(= v 2)} = ([Int] length) tup2 in
let _ :: Int = ([Int] geti) tup2 0 in
let _ :: Int = ([Int] geti) tup2 1 in
let _ :: {(= v undefined)} = ([Int] geti) tup2 2 in

0
