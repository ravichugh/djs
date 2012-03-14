
val impGetProp ::
  {(and (v :: [; L; H]
              _:[x:Ref(L), k:Str] / [H ++ L |-> d:{Dict|(has v k)}]
           -> {(= v (sel d k))} / same)
        (v :: [A; L; H]
              _:[x:Ref(L), i:{Str|(= v "length")}] / [H ++ L |-> a:Arr(A)]
           -> {Int|(implies (packed a) (= v (len a)))} / same))}

val impGetArr :: [A;L] _:[x:Ref(L), i:Int] / [L |-> a:Arr(A)] ->
  {(ite (and (packed a) (>= i 0))
        (ite (< i (len a)) (and (v::A) (= v (sel a i))) (= v undefined))
        (or (v::A) (= v undefined)))} / same

