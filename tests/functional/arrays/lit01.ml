
#use "tests/functional/arrays/__arrays.ml"

let tup0 = <> as Arr(IntOrBool) in
let tup1 = ([IntOrBool] push) tup0 17 in

let tup2 = <1, true> as Arr(IntOrBool) in
let tup3 = ([IntOrBool] push) tup2 17 in

let _ :: {(= (len v) 0)} = tup0 in
let _ :: {(= (len v) 1)} = tup1 in
let _ :: {(= (len v) 2)} = tup2 in
let _ :: {(= (len v) 3)} = tup3 in

0
