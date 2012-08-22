
open Lang

val emitPreamble : unit -> unit

val queryCount : int ref

val queryRoot : string ref

val writeQueryStats : unit -> unit

val doingExtract : bool ref

val dump : ?nl:bool -> ?tab:bool -> string -> unit

val inNewScope : (unit -> 'a) -> 'a

val assertFormula : formula -> unit

val addBinding : string -> typ -> unit

val falseIsProvable : string -> bool

val checkValid : string -> formula -> bool

