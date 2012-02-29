
(******************************************************************************)

let global = ref lGlobal {}

(* checking that JS tags get munged correctly by Lang.switchJsString *)
let jsTagInt  :: {(= "Int"  "number")} = 0
let jsTagBool :: {(= "Bool" "boolean")} = 0
let jsTagStr  :: {(= "Str"  "string")} = 0
let jsTagDict :: {(= "Dict" "object")} = 0


(***** Object.prototype *******************************************************)

(* in lang.ml and tcDref.ml right now. *)


(***** Array.prototype ********************************************************)

val __ArrayProto_push :: {(= v "push")}

val __ArrayProto_pop :: Top

let __ArrayProtoDict =
  { "push" = __ArrayProto_push
  ; "pop"  = __ArrayProto_pop
  }

let __ArrayProto = new (__ArrayProtoDict, lArrayProto, __Object, lObject)

(*
(* use __Function? *)
let __Array = new ({"prototype" = __ArrayProto}, lArray, __Object, lObject)
*)


(***** Full Objects / Arrays **************************************************)

(**  [[ x.f  ]] = getProp ([[x]],   f  )                                     **)
(**  [[ x[i] ]] = getIdx  ([[x]],   i  )                                     **)
(**  [[ x[k] ]] = getElem ([[x]], [[k]])                                     **)
(**                                                                          **)
(**     where i is an integer literal, k is not an integer literal           **)

val getPropObj :: [; L1,L2; H]
     _:[x:Ref(L1), k:Str] / [H ++ L1 |-> (d:{Dict|ObjHas([v],k,H,L2)}, L2)]
  -> {(= v ObjSel([d],k,H,L2))} / same

(* tempting to write down getPropArr for "length" and non-"length" separately
   and then use an intersection, but that's no good for the type checker. *)
val getPropArr :: [A; L1,L2; H]
     _:[x:Ref(L1), k:Str] / [H ++ L1 |-> (a:Arr(A), L2)]
  -> {(ite (= k "length")
           (and (v:Int) (implies (packed a) (= v (len a))))
           (= v HeapSel(H,L2,k)))} / same

val getPropArrLen :: [A; L1,L2; H]
     _:[x:Ref(L1), k:{(= v "length")}] / [H ++ L1 |-> (a:Arr(A), L2)]
  -> {Int|(implies (packed a) (= v (len a)))} / same

val getIdx :: [A; L1,L2; H]
     _:[x:Ref(L1), i:Int] / [H ++ L1 |-> (a:Arr(A), L2)]
  -> {(ite (and (packed a) (>= i 0))
           (ite (< i (len a)) (and (v::A) (= v (sel a i))) (= v undefined))
           (or (v::A) (= v undefined)))} / same

val getProp :: {(and (type getPropObj) (type getPropArr))}

val getElem :: {(and (type getPropObj) (type getPropArrLen) (type getIdx))}
  (* note that the non-"length" part of getPropArr is _not_ included
     in this intersection *)

(******************************************************************************)

let end_of_djs_prelude :: INT = 0

