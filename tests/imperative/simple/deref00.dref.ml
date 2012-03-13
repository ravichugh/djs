
let foo :: [;L] x:Ref(L) / [L|->y:TOP] -> {(= v y)} / [L|->z:TOP] =
  fun x ->
    (!x)
in

0
