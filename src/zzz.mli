
open Lang

val emitPreamble : unit -> unit

val queryCount : int ref

val queryRoot : string ref

val writeQueryStats : unit -> unit

val doingExtract : bool ref

val dump : ?nl:bool -> ?tab:bool -> string -> unit

(* val pushScope : unit -> unit *)

(* val popScope : unit -> unit *)

val inNewScope : (unit -> 'a) -> 'a

val assertFormula : formula -> unit

val addBinding : ?isNew:bool -> string -> formula -> unit

val removeBinding : unit -> unit

val falseIsProvable : string -> bool

val checkValid : string -> formula -> bool

