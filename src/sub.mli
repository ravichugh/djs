
open Lang

(***** Meet/Join **************************************************************)

val doMeet : bool ref

val maxJoinSize : int ref

val meetAll : TypeTerms.t -> typterm option

val joinAll : TypeTerms.t -> typterm option

(* val simpleHeapJoin : value -> heap -> heap -> heap *)

(***** Extraction *************************************************************)

val mustFlow : ?filter:(typterm -> bool) -> env -> typ -> TypeTerms.t

val canFlow : ?filter:(typterm -> bool) -> env -> typ -> TypeTerms.t

val writeStats : unit -> unit

(***** Subtyping **************************************************************)

val types : string -> env -> typ -> typ -> unit

val heapSat : string -> env -> heapenv -> heap -> LangUtils.vsubst

val worldSat : string -> env -> typ * heapenv -> world -> LangUtils.vsubst

(*
val heaps : string -> ?locsOpt:(loc list option) -> env -> heap -> heap
  -> LangUtils.vsubst

val worlds : string -> env -> world -> world -> LangUtils.vsubst
*)

