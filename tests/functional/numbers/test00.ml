
let _ :: {(= v 3)} = js_plus (1, 2) in

let _ :: {(= v (+ 1 2))} = js_plus (1, 2) in

let _ :: {(= (tag v) "number")} = js_plus (1, 2) in

let _ :: Num = js_plus (1, 2) in

let _ :: {(integer v)} = js_plus (1, 2) in

let _ :: Int = js_plus (1, 2) in

0
