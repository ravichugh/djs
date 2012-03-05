let foo :: [;L] x:Ref(L) / [L |-> n:Int] -> Int / same =
  ([ [;L] x:Ref(L) / [L |-> n:Int] -> Int / same] fix)
    (fun f ->
      (fun i -> (([;L;] f) (i))))
in 0
