
open Lang

val argSpecs : (Arg.key * Arg.spec * Arg.doc) list

(* val mkTupleTyp : typ list -> typ *)

(*

(* TODO factor this type and mkFixFun with uarr type *)

val mkDepTupleArrow :
  (vvar list * typ) -> (heap * typ * heap) -> (vvar * typ * heap * typ * heap)

*)

(* val mkDepTupleTyp : (vvar * typ) list -> typ *)

val mkTupleExp : exp list -> exp

val addLets : exp -> (vvar * exp) list -> exp

val mkPatFun : pat -> exp -> value

val maybeAddHeapPrefixVar : uarrow -> uarrow

val typToFrame : typ -> frame

(* val mkLetRec : vvar -> uarrow -> exp -> exp -> exp *)

val mkLetRec_ : vvar -> uarrow -> exp -> exp -> exp

val doIntersectionHack : vvar -> formula

val undoIntersectionHack : env -> typ -> typ 

