
open Lang

val tsVal : env -> heap -> value -> typ

val tsExp : env -> heap -> exp -> world

val tcVal : env -> heap -> typ -> value -> unit

val tcExp : env -> heap -> world -> exp -> unit

val typecheck : exp -> unit

