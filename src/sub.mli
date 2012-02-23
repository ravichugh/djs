
open Lang

(***** Meet/Join **************************************************************)

val doMeet : bool ref

val maxJoinSize : int ref

val meetAll : TypeTerms.t -> typterm option

val joinAll : TypeTerms.t -> typterm option

(* TODO *)

val simpleHeapJoin : value -> heap -> heap -> heap

(***** Extraction *************************************************************)

val mustFlow : ?filter:(typterm -> bool) -> env -> typ -> TypeTerms.t

val canFlow : ?filter:(typterm -> bool) -> env -> typ -> TypeTerms.t

(***** Subtyping **************************************************************)

val types : string -> env -> typ -> typ -> unit

val heaps : string -> env -> heap -> heap -> LangUtils.vsubst

val worlds : string -> env -> world -> world -> LangUtils.vsubst

