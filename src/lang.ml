
(*****************************************************************************)

exception Parse_error of string
exception Z3_read_error of string
exception Tc_error of string list

let err s = raise (Tc_error s)
let z3err s = raise (Z3_read_error s)
let kill s = Printf.fprintf stderr "\nFATAL ERROR\n\n%s\n" s; exit 1

(* for current nesting during type checking *)
let depth = ref 0
let indent () = String.make (2 * !depth) ' '
let bigindent () = String.make (4 * !depth) ' '


(*****************************************************************************)

type pos = Lexing.position * Lexing.position
let pos0 = (Lexing.dummy_pos, Lexing.dummy_pos)

type tag = string

let tagDict  = "Dict"      (* for internal functional dictionaries *)
let tagRef   = "Ref"       (* for internal references *)
(* let tagArray = "Array"     (* for internal functional arrays *) *)
let tagNum   = "number"
let tagBool  = "boolean"
let tagStr   = "string"
let tagObj   = "object"
let tagUndef = "undefined"
let tagFun   = "function"

type vvar   = string
type tvar   = string
type lvar   = string
type hvar   = string
type lbl    = string

type vvars  = vvar list
type tvars  = tvar list
type lvars  = lvar list
type hvars  = hvar list

type lconst = string
type loc    = LocVar of lvar | LocConst of lconst
type locs   = loc list
type thawstate = Frzn | Thwd of loc

type pat =
  | PLeaf of vvar
  | PNode of pat list

type exp =
  (***** core expressions *****)
  | EVal of value
  | EDict of (exp * exp) list
  | EArray of typ * exp list
  | EFun of (tvars * lvars * hvars) * vvar * (typ * heap) option * exp
  | EIf of exp * exp * exp
  | EApp of (typs * locs * heaps) * exp * exp
  | ELet of vvar * frame option * exp * exp
  | EExtern of vvar * typ * exp
  | ETcFail of string * exp
  | EAs of string * exp * frame           (* string carries debug info *)
  | EAsW of string * exp * world          (* string carries debug info *)
  (***** reference operations *****)
  | ENewref of loc * exp
  | EDeref of exp
  | ESetref of exp * exp
  | EFreeze of loc * thawstate * exp
  | EThaw of loc * exp
  | EWeak of weakloc * exp
  (***** control operators *****)
  | ELabel of lbl * exp
  | EBreak of lbl * exp
  | EThrow of exp
  | ETryCatch of exp * vvar * exp
  | ETryFinally of exp * exp
  (***** create a proto-based object or array *****)
  | ENewObj of exp * loc * exp * loc
  (***** helpers for parsing *****)
  | ELoadSrc of string * exp         (* inserted/eliminated by parsing *)
  | ELoadedSrc of string * exp       (* placeholder to indicate source file *)
  (***** abstract sugar *****)
  (* TODO add tuples, DJS App nodes, ... ***)

and value_ =
  | VBase of basevalue
  | VVar of vvar
  | VEmpty
  | VExtend of value * value * value
  | VArray of typ * value list (* TODO okay to drop typ? *)
  | VFun of (tvars * lvars * hvars) * vvar * (typ * heap) option * exp
  | VNewObjRef of int

and value = { pos: pos; value: value_ }

and basevalue =
  | Int of int
  | Str of string
  | Bool of bool
  | Null
  | Undef

and walue = (* logical values *)
  | WVal of value
  | WApp of string * walue list
  | WHeapSel of heap * loc * walue 
  | WBot
  (***** special macro walue *****)
  | WObjSel of wobjsel

and wobjsel = walue list * walue * heap * loc

and formula =
  (***** simple predicates *****)
  | PEq of walue * walue
  | PTru
  | PFls
  (***** uninterpreted predicates *****)
  | PHasTyp of hastyp
  | PHeapHas of heap * loc * walue
  (***** simple/uninterpreted predicates *****)
  | PApp of string * walue list
  (***** logical connectives *****)
  | PConn of string * formula list
  (***** quantifiers for dictionary expanding macros *****)
  | PAll of string * formula
  (***** delayed macros *****)
  | PHas of walue * walue list
  | PDomEq of walue * walue list
  | PEqMod of walue * walue * walue list
  | PObjHas of walue list * walue * heap * loc

and hastyp = walue * typterm

and rawtyp = vvar * formula (* {x|p} *)

and typ =
  | TRefinement of rawtyp
  (***** delayed macros *****)
  | TTop | TBot
  | TBaseUnion of tag list
  | TBaseRefine of vvar * tag * formula
  | TInt
  (* TODO remove the formula part, since that's what TSelfify does *)
  | THasTyp of typterm list * formula (* {v | v::U_1 /\ ... /\ v::U_n /\ p} *)
  | TTuple of (vvar * typ) list
  | TNonNull of typ
  | TMaybeNull of typ
  | TSelfify of typ * formula (* { v | T(v) /\ p } *)
  (***** created during type checking *****)
  | TExists of vvar * typ * typ

and uarrow = (tvars * lvars * hvars) * vvar * typ * heap * typ * heap

and typterm =
  | UArrow  of uarrow
  | UVar    of tvar
  | URef    of loc
  | UNull
  | UArray  of typ

and heapconstraint =
  | HConc    of vvar option * typ        (* [l |-> x:S]       *)
  | HConcObj of vvar option * typ * loc  (* [l |-> (x:S, l')] *)
  | HWeakTok of thawstate                (* [m |-> 0]         *)

and heap  = hvars * (loc * heapconstraint) list
and world = typ * heap
and frame = hvars * heap * world
and typs  = typ list
and heaps = heap list

and weakloc = loc * typ * loc (* m |-> (T, l) *)

(* differences compared to formal presentation:
   - patterns for (abstract) syntactic sugar
   - formulas are not a kind of environment binding since they will be
     pushed/popped incrementally
   - keeping label names in here rather than separate environment
*)
type envbinding =
  | Var  of vvar * typ
  | TVar of tvar
  | LVar of lvar
  | HVar of hvar
  | Lbl  of lbl * world option
  | WeakLoc of weakloc

type env = envbinding list

and heapenvconstraint =
  | HEConc    of value        (* [l |-> v]      *)
  | HEConcObj of value * loc  (* [l |-> (v,l')] *)
  | HEWeakTok of thawstate    (* [m |-> 0]      *)

type heapenv = hvars * (loc * heapenvconstraint) list

type clause = formula * hastyp list

module TypeTerms =
  Set.Make (struct type t = typterm let compare = compare end)

let mkTypeTerms l =
  List.fold_left (fun acc ut -> TypeTerms.add ut acc) TypeTerms.empty l

let wrapVal pos value = { pos = pos; value = value }

let lRoot = LocConst "lROOT"
let lObjectPro = LocConst "lObjectProto"

let isWeakLoc = function LocConst(x) | LocVar(x) -> x.[0] = '~'
let isStrongLoc l = not (isWeakLoc l)

