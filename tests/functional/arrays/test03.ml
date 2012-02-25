
#use "tests/functional/arrays/arrays.ml"

val tup4 :: {(and (v::Arr({(or (v:Int) (v:Bool) (v:Str))}))
                  (packed v) (= (len v) 4)
                  ((sel v 0) : Int)
                  ((sel v 1) : Bool))}

let _ :: Int =
  ([{(or (v:Int) (v:Bool) (v:Str))}] geti) tup4 0 in

let _ :: Bool =
  ([{(or (v:Int) (v:Bool) (v:Str))}] geti) tup4 1 in

let _ :: {(or (v:Int) (v:Bool) (v:Str))} =
  ([{(or (v:Int) (v:Bool) (v:Str))}] geti) tup4 2 in

let _ :: {(or (v:Int) (v:Bool) (v:Str))} =
  ([{(or (v:Int) (v:Bool) (v:Str))}] geti) tup4 3 in

let _ :: {(= v undefined)} =
  ([{(or (v:Int) (v:Bool) (v:Str))}] geti) tup4 4 in

0

