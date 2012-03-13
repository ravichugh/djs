
let begin_main = 0 in

let a = ref loc1 0 in

let b = !a in

let _ :: {(= v 0)} = b in

let c = a := 1 in

let d = !a in

let _ :: {(= v 1)} = d in

(* this forces variable elim even for ERef rule *)
let e = a := b in

0
