
val i :: {Int|(and (>= v 0) (< v 1))}
let _ :: {(= v 0)} = i in

val j :: {Int|(and (>= v 0) (< v 2))}
let _ :: Num = j in
let _ :: Int = j in
let _ :: {(or (= v 0) (= v 1))} = j in

0
