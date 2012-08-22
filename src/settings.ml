
let djs_dir =
  try
    let s = Unix.getenv "DJS_DIR" in
    if s.[String.length s - 1] = '/' then s
    else s ^ "/" (* ensuring trailing '/' *)
  with Not_found ->
    Lang.kill "Set and export the environment variable DJS_DIR \
               to the root of the DJS directory"

let out_dir  = djs_dir ^ "src/out/"
let prim_dir = djs_dir ^ "prims/"

let strictWarn = ref true
let printAllTypes = ref false
let useTheoryLA = ref true
let marshalOutEnv = ref false
let marshalInEnv = ref false
let doFalseChecks = ref false

let tryAllBoxesHack = ref false

(* DJS options *)
let djsMode = ref false
let doVarLifting = ref false
let doImplicitGlobal = ref false
let fullObjects = ref true
let doArgsArray = ref false

(* TODO rename this since it only applies to desugaring obj prims *)
let typedDesugaring = ref true
(*
let inferFrames = ref false
let monotonicHeaps = ref false
*)
let augmentHeaps = ref false
let greedyThaws = ref false
let assistCtor = ref false

