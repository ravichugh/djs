
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
              _:[_:Ref(L), k:Str] / [H ++ L |-> d:{Dict|(has v k)}]
           -> {(= v (sel d k))} / same)
        (v :: [A; L; H]
              _:[_:Ref(L), i:{Str|(= v "length")}] / [H ++ L |-> a:Arr(A)]
           -> {Int|(implies (packed a) (= v (len a)))} / same))}

val getIdxLite :: [A;L] _:[_:Ref(L), i:Int] / [L |-> a:Arr(A)] ->
  {(ite (and (packed a) (>= i 0))
        (ite (< i (len a)) (and (v::A) (= v (sel a i))) (= v undefined))
        (or (v::A) (= v undefined)))} / same

val getElemLite :: {(and (type getPropLite) (type getIdxLite))}

val setPropLite ::
  {(and (v :: [;L]
              _:[_:Ref(L), k:Str, y:Top] / [L |-> d:Dict]
           -> {(= v y)} / [L |-> d':{(= v (upd d k y))}])
        (v :: [A;L]
              _:[_:Ref(L), k:{(= v "length")}, n:Int] / [L |-> a:Arr(A)]
           -> {(= v n)}
            / [L |-> a':{(and (v::Arr(A))
                              (implies (and (packed a) (<= n (len a)))
                                       (and (packed v) (= (len v) n))))}]))}

val setIdxLite :: [A;L] _:[_:Ref(L), i:Int, y:A] / [L |-> a:Arr(A)] ->
  {(= v y)} /
  [L |-> a':{(and (v::Arr(A))
                  (= (sel a i) y)
                  (implies (and (packed a) (>= i 0) (< i (len a)))
                           (and (packed v) (= (len v) (len a))))
                  (implies (and (packed a) (= i (len a)))
                           (and (packed v) (= (len v) (+ 1 (len a))))))}]

val setElemLite :: {(and (type setPropLite) (type setIdxLite))}


(******************************************************************************)

let end_of_djs_prelude :: INT = 0

