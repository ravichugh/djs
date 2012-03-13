
(* multiple reads with no intervening writes *)

let foo :: [;L] x:Ref(L) / [L|->yy:Top] -> {(= v true)} / [L|->_:{(= v yy)}] =
  fun x ->
    (js_eek (!x) (!x))
in

0
