
(******************************************************************************)

let global = ref lGlobal {}

(* checking that JS tags get munged correctly by Lang.switchJsString *)
let jsTagInt  :: {(= "Int"  "number")} = 0
let jsTagBool :: {(= "Bool" "boolean")} = 0
let jsTagStr  :: {(= "Str"  "string")} = 0
let jsTagDict :: {(= "Dict" "object")} = 0


(***** Lite Objects / Arrays **************************************************)

val getPropLite ::
  {(and (v :: [; L; H]
              _:[x:Ref(L), k:Str] / [H ++ L |-> d:{Dict|(has v k)}]
           -> {(= v (sel d k))} / same)
        (v :: [A; L; H]
              _:[x:Ref(L), i:{Str|(= v "length")}] / [H ++ L |-> a:Arr(A)]
           -> {Int|(implies (packed a) (= v (len a)))} / same))}

val getIdxLite :: [A;L] _:[x:Ref(L), i:Int] / [L |-> a:Arr(A)] ->
  {(ite (and (packed a) (>= i 0))
        (ite (< i (len a)) (and (v::A) (= v (sel a i))) (= v undefined))
        (or (v::A) (= v undefined)))} / same

val getElemLite :: (* combines getPropLite and getIdxLite *)
  {(and (v :: [; L; H]
              _:[x:Ref(L), k:Str] / [H ++ L |-> d:{Dict|(has v k)}]
           -> {(= v (sel d k))} / same)
        (v :: [A; L; H]
              _:[x:Ref(L), i:{Str|(= v "length")}] / [H ++ L |-> a:Arr(A)]
           -> {Int|(implies (packed a) (= v (len a)))} / same)
        (v :: [A;L] _:[x:Ref(L), i:Int] / [L |-> a:Arr(A)]
           -> {(ite (and (packed a) (>= i 0))
                    (ite (< i (len a))
                              (and (v::A) (= v (sel a i)))
                              (= v undefined))
                    (or (v::A) (= v undefined)))} / same))}


(******************************************************************************)

let end_of_djs_prelude :: INT = 0

