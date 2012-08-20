
open Lang

val emitPreamble : unit -> unit

val queryCount : int ref

val queryRoot : string ref

val writeQueryStats : unit -> unit

val doingExtract : bool ref

val dump : ?nl:bool -> ?tab:bool -> string -> unit

val pushScope : unit -> unit

val popScope : unit -> unit

val assertFormula : formula -> unit

(* TODO remove? *)
val pushForm : formula -> unit

(* TODO remove? *)
val popForm : unit -> unit

(* val addTypeVar : string -> unit *)

(* TODO combine add and push versions *)

val addBinding : ?isNew:bool -> string -> formula -> unit

val removeBinding : unit -> unit

(* TODO remove? *)
val pushBinding : string -> formula -> unit

(* TODO remove? *)
val popBinding : unit -> unit

val falseIsProvable : string -> bool

val checkValid : string -> formula -> bool

