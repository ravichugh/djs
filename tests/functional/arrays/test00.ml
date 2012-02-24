
(***** lame arrays ************************************************************)

(* just for experimenting. every read produces a possibly null value *)

val _newarr :: [A] _:Top -> Arr(A)

val _geti :: [A] a:Arr(A) -> i:Int -> {(or (v::A) (= v null))}

val _seti :: [A] a:Arr(A) -> i:Int -> x:A -> Arr(A)

val _length :: [A] a:Arr(Top) -> Int

val _append :: [A] a:Arr(A) -> x:A -> Arr(A)

(******************************************************************************)

let tops = ([Top] _newarr) 0 in
let _ = ([Top] _geti) tops 1 in

let ints = ([Int] _newarr) 10 in
let _ :: {(or (= v null) (v : Int))} = ([Int] _geti) ints 1 in
0

