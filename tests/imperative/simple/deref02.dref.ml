
let foo :: [;L] xx:Ref(L) / [L|->yy:Int] -> Int / [L|->_:{(= v yy)}] =
  fun xx ->
    (js_plus (!xx) 1)
in

0
