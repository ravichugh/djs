
open Lang

(* val mkTupleTyp : typ list -> typ *)

(*

(* TODO factor this type and mkFixFun with uarr type *)

val mkDepTupleArrow :
  (vvar list * typ) -> (heap * typ * heap) -> (vvar * typ * heap * typ * heap)

*)

(* val mkDepTupleTyp : (vvar * typ) list -> typ *)

val mkTupleExp : exp list -> exp

val mkPatFun : (tvars * lvars * hvars) -> pat -> exp -> exp

val maybeAddHeapPrefixVar : uarr -> uarr

val typToFrame : typ -> frame

(*
val mkLetRec : vvar -> typ -> exp -> exp -> exp

val mkLetRecMono :
  vvar -> (locs * vvar * typ * heap * typ * heap) -> exp -> exp -> exp
*)

