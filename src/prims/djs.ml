
(******************************************************************************)

let global = ref lGlobal {}

(* checking that JS tags get munged correctly by Lang.switchJsString *)
let jsTagInt  :: {(= "Int"  "number")} = 0
let jsTagBool :: {(= "Bool" "boolean")} = 0
let jsTagStr  :: {(= "Str"  "string")} = 0
let jsTagDict :: {(= "Dict" "object")} = 0


(******************************************************************************)

let end_of_djs_prelude :: INT = 0

