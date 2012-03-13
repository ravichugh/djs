val ____ObjectProto :: Ref(lObjectProto)

weak [~lWeak |-> (frzn, {((sel v "f") : Int)}, lObjectProto)]

let strong_obj_1 = new ({"f" = 100}, lStrong1, ____ObjectProto, lObjectProto) in
let weak_obj_1   = freeze (~lWeak, strong_obj_1) in

let strong_obj_2 = new ({"f" = true}, lStrong2, ____ObjectProto, lObjectProto) in
let _ :: Int = ([;lStrong2,lObjectProto;] setPropObj) (strong_obj_2, "f", 200) in
let weak_obj_2 = freeze (~lWeak, strong_obj_2) in

let _ :: Ref(~lWeak) = weak_obj_1 in
let _ :: Ref(~lWeak) = weak_obj_2 in
let _ :: {(not (= v null))} = weak_obj_1 in
let _ :: {(not (= v null))} = weak_obj_2 in

0