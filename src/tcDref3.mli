
open Lang

val tsVal : env -> heapenv -> value -> typ

val tsExp : env -> heapenv -> exp -> (prenextyp * heapenv)

val tcVal : env -> heapenv -> typ -> value -> unit

val tcExp : env -> heapenv -> world -> exp -> unit

val typecheck : exp -> unit

