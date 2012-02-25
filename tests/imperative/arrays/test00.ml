
#use "tests/imperative/arrays/__arrays.ml"

let d = ref lD {"f" = 1} in
let _ :: {(= v 1)} = ([;lD] impGetProp) (d, "f") in

let a = ref lA <0, 1> in
let _ :: {(= v 2)} = ([Top;lA] impGetProp) (a, "length") in
let _ :: {(= v 0)} = ([Top;lA] impGetArr) (a, 0) in
let _ :: {(= v 1)} = ([Top;lA] impGetArr) (a, 1) in
let _ :: {(= v undefined)} = ([Top;lA] impGetArr) (a, 2) in

0
