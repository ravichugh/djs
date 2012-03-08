
(***** DJS tag-test ***********************************************************)

val js_typeof1 :: [[x:{(or (= (tag v) "number")
                           (= (tag v) "boolean")
                           (= (tag v) "string")
                           (= v undefined) (= v null))}]]
  -> {Str|(ite (= v null) (= v "object") (= v (tag x)))}

(* note: not treating functions as objects right now *)
val js_typeof2 ::
  [;L1,L2] [[_:Ref(L1)]] / [L1 |-> (y:Top, L2)] -> {(= v "object")} / same

val js_typeof :: {(and (type js_typeof1) (type js_typeof2))}


(***** Full Objects / Arrays **************************************************)

(**    [[ x.f    ]] = getProp ([[x]],  "f" )                                 **)
(**    [[ x["f"] ]] = getProp ([[x]],  "f" )    where "f" is a SafeStr       **)
(**    [[ x[i]   ]] = getIdx  ([[x]],   i  )    where i is an int literal    **)
(**    [[ x[k]   ]] = getElem ([[x]], [[k]])    where k is anything else     **)

val getPropObj :: [; L1,L2; H]
     [[x:Ref(L1), k:Str]] / [H ++ L1 |-> (d:Dict, L2)]
  -> {(ite (objhas d k H L2) (= v (objsel d k H L2)) (= v undefined))} / same

(* tempting to write down getPropArr for "length" and non-"length" separately
   and then use an intersection, but that's no good for the type checker. *)
val getPropArr :: [A; L1,L2; H]
     [[x:Ref(L1), k:Str]] / [H ++ L1 |-> (a:Arr(A), L2)]
  -> {(ite (= k "length")
           (and (v:Int) (implies (packed a) (= v (len a))))
           (ite (heaphas H L2 k)
                (= v (heapsel H L2 k))
                (= v undefined)))} / same

val getPropArrLen :: [A; L1,L2; H]
     [[x:Ref(L1), k:{(= v "length")}]] / [H ++ L1 |-> (a:Arr(A), L2)]
  -> {Int|(implies (packed a) (= v (len a)))} / same

val getIdx :: [A; L1,L2; H]
     [[x:Ref(L1), i:Int]] / [H ++ L1 |-> (a:Arr(A), L2)]
  -> {(ite (and (packed a) (>= i 0))
           (ite (< i (len a)) (and (v::A) (= v (sel a i))) (= v undefined))
           (or (v::A) (= v undefined)))} / same

val getProp :: {(and (type getPropObj) (type getPropArr))}

val getElem :: {(and (type getPropObj) (type getPropArrLen) (type getIdx))}
  (* note that the non-"length" part of getPropArr is _not_ included
     in this intersection *)

(**    [[ x.f  = y ]] = setProp ([[x]],  "f" , [[y]])                        **)
(**    [[ x[i] = y ]] = setIdx  ([[x]],   i  , [[y]])                        **)
(**    [[ x[k] = y ]] = setElem ([[x]], [[k]], [[y]])                        **)

val setPropObj :: [; L1,L2; H]
     [[x:Ref(L1), y:Str, z:Top]] / [H ++ L1 |-> (d:Dict, L2)]
  -> {(= v z)} / [H ++ L1 |-> (d':{(= v (upd d y z))}, L2)]

val setPropArrLen :: [A; L1,L2]
     [[_:Ref(L1), k:{(= v "length")}, n:Int]] / [L1 |-> (a:Arr(A), L2)]
  -> {(= v n)}
   / [L1 |-> (a':{(and (v::Arr(A))
                       (implies (and (packed a) (<= n (len a)))
                                (and (packed v) (= (len v) n))))}, L2)]

val setIdx :: [A; L1,L2]
     [[_:Ref(L1), i:Int, y:A]] / [L1 |-> (a:Arr(A), L2)]
  -> {(= v y)}
   / [L1 |-> (a':{(and (v::Arr(A))
                  (= (sel a i) y)
                  (implies (and (packed a) (>= i 0) (< i (len a)))
                           (and (packed v) (= (len v) (len a))))
                  (implies (and (packed a) (= i (len a)))
                           (and (packed v) (= (len v) (+ 1 (len a))))))}, L2)]

val setProp :: {(and (type setPropObj) (type setPropArrLen))}

val setElem :: {(and (type setPropObj) (type setPropArrLen) (type setIdx))}

(**    [[  i  in x ]] = hasIdx  ([[x]],   i  )                                 **)
(**    [[ "f" in x ]] = hasProp ([[x]],  "f" )    where "f" is a SafeStr       **)
(**    [[  k  in x ]] = hasElem ([[x]], [[k]])                                 **)

val hasPropObj :: [; L1,L2; H]
     [[x:Ref(L1), k:Str]] / [H ++ L1 |-> (d:Dict, L2)]
  -> {Bool|(iff (= v true) (objhas d k H L2))} / same

val hasPropArr :: [A; L1,L2; H]
     [[x:Ref(L1), k:Str]] / [H ++ L1 |-> (a:Arr(A), L2)]
  -> {Bool|(iff (= v true) (or (= k "length") (heaphas H L2 k)))} / same

val hasPropArrLen :: [A; L1,L2; H]
     [[x:Ref(L1), k:{(= v "length")}]] / [H ++ L1 |-> (a:Arr(A), L2)]
  -> {(= v true)} / same

val hasIdx :: [A; L1,L2]
     [[_:Ref(L1), i:Int]] / [L1 |-> (a:Arr(A), L2)]
  -> {Bool|(implies (and (packed a) (>= i 0))
                    (iff (= v true) (< i (len a))))} / same

val hasProp :: {(and (type hasPropObj) (type hasPropArr) (type hasIdx))}

val hasElem :: {(and (type hasPropObj) (type hasPropArrLen) (type hasIdx))}


(******************************************************************************)

let end_of_djs_prelude :: INT = 0

