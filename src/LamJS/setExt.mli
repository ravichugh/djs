(** Additional functions for working with sets. *)

open Format
open FormatExt

module type S = sig
  type elt
  type t

  val unions : t list -> t
  val from_list : elt list -> t
  val to_list : t -> elt list
  val p_set : (elt -> printer) -> t -> printer

end

module Make : functor (Set : Set.S) -> S 
  with type elt = Set.elt 
  and type t = Set.t
