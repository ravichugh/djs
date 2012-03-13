
let foo :: [;L] x:Ref(L) / [L|->y:Top]
             -> Top      / [L|->z:{(= v y)}] =
  fun x ->
    (x := (!x))
in

0
