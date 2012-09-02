
#use "tests/functional/arrays/__arrays.ml"

val tup4 :: {(and (v::Arr({(or (Int v) (Bool v) (Str v))}))
                  (packed v) (= (len v) 4)
                  (Int (sel v 0))
                  (Bool (sel v 1)))}

let _ :: Int =
  ([{(or (Int v) (Bool v) (Str v))}] geti) tup4 0 in

let _ :: Bool =
  ([{(or (Int v) (Bool v) (Str v))}] geti) tup4 1 in

let _ :: {(or (Int v) (Bool v) (Str v))} =
  ([{(or (Int v) (Bool v) (Str v))}] geti) tup4 2 in

let _ :: {(or (Int v) (Bool v) (Str v))} =
  ([{(or (Int v) (Bool v) (Str v))}] geti) tup4 3 in

let _ :: {(= v undefined)} =
  ([{(or (Int v) (Bool v) (Str v))}] geti) tup4 4 in

0

