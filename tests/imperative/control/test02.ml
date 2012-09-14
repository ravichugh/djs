let id :: x:Top -> {(= v x)} =
  fun x -> ( #return { let y = break #return x in undefined }) in

let _ :: {(= v 1)} = id 1 in
let _ :: {(= v 2)} = id 2 in
let _ :: {(= v true)} = id true in
0
