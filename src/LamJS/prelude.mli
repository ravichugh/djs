(*****************************************************************************)
(*  Original: LambdaJS                                                       *)
(*  Modified: Ravi Chugh (rkc) (rchugh@cs.ucsd.edu)                          *)
(*****************************************************************************)

(* rkc: added these two opens *)
open SetExt
open MapExt

type id = string

type pos = Lexing.position * Lexing.position

module Pos : sig
  type t = pos
  val compare : t -> t -> int
  val before : t -> t -> bool
end


module IntSet : Set.S
  with type elt = int

module IntSetExt : SetExt.S
  with type elt = int
  and type t = IntSet.t

module IdSet : Set.S 
  with type elt = id

module IdSetExt : SetExt.S 
  with type elt = id 
  and type t = IdSet.t

module PosSet : Set.S 
  with type elt = pos

module PosSetExt : SetExt.S 
  with type elt = pos
  and type t = PosSet.t

module PosMap : Map.S
  with type key = pos

module PosMapExt : MapExt.S
  with type key = pos
  with type +'a t = 'a PosMap.t

module IdMap : Map.S
  with type key = id

module IdMapExt : MapExt.S
  with type key = id
  with type +'a t = 'a IdMap.t


val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a

val fold_right : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b

val map : ('a -> 'b) -> 'a list -> 'b list

val second2 : ('b -> 'c) -> 'a * 'b -> 'a * 'c

val third3 : ('c -> 'd) -> 'a * 'b * 'c -> 'a * 'b * 'd

val string_of_position : pos -> string

val snd3 : 'a * 'b * 'c -> 'b

val snd2 : 'a * 'b -> 'b

val fst2 : 'a * 'b -> 'a

val fst3 : 'a * 'b * 'c -> 'a

val thd3 : 'a * 'b * 'c -> 'c

val printf : ('a, out_channel, unit) format -> 'a

val eprintf : ('a, out_channel, unit) format -> 'a

val sprintf : ('a, unit, string) format -> 'a

val intersperse : 'a -> 'a list -> 'a list

val take_while : ('a -> bool) -> 'a list -> 'a list * 'a list

val match_while : ( 'a -> 'b option) -> 'a list -> 'b list * 'a list

(** [nub lst] removes duplicates from the [lst]. Duplicates are identified by
    structural equality. *)
val nub : 'a list -> 'a list

(** [iota n] returns the list of integers [0] through [n-1], inclusive. *)
val iota : int -> int list
