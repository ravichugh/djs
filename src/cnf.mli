
open Lang

val orHasTyps : hastyp list -> formula

val checkConversion : bool ref

val convert : formula -> clause list

