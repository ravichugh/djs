
open Lang

(* val mkTupleTyp : typ list -> typ *)

(*

(* TODO factor this type and mkFixFun with uarr type *)

val mkDepTupleArrow :
  (vvar list * typ) -> (heap * typ * heap) -> (vvar * typ * heap * typ * heap)

*)

(* val mkDepTupleTyp : (vvar * typ) list -> typ *)

val mkTupleExp : exp list -> exp

val addLets : exp -> (vvar * exp) list -> exp

val mkPatFun : (tvars * lvars * hvars) -> pat -> exp -> exp

val maybeAddHeapPrefixVar : uarr -> uarr

val typToFrame : typ -> frame

val mkLetRec : vvar -> uarr -> exp -> exp -> exp

val doIntersectionHack : vvar -> formula

val undoIntersectionHack : env -> typ -> typ 

