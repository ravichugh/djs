let id :: x:Top -> {(= v x)} =
  fun x -> ( #return { break #return x }) in

let _ :: {(= v 1)} = id 1 in
let _ :: {(= v 2)} = id 2 in
let _ :: {(= v true)} = id true in
0
