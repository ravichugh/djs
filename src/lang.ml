
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
  | EFun of pat * exp
  | EIf of exp * exp * exp
  | EApp of (typs * locs * heaps) * exp * exp
  | ELet of vvar * frame option * exp * exp
  (***** abstract syntactic sugar *****)
  | ETuple of exp list
  (***** reference operations *****)
  | ENewref of loc * exp * closureinvariant
  | EDeref of exp
  | ESetref of exp * exp
  | ENewObj of exp * loc * exp * loc * closureinvariant
  | EFreeze of loc * thawstate * exp
  | EThaw of loc * exp
  | EWeak of weakloc * exp
  (***** control operators *****)
  | ELabel of lbl * exp
  | EBreak of lbl * exp
  | EThrow of exp
  | ETryCatch of exp * vvar * exp
  | ETryFinally of exp * exp
  (***** external definitions *****)
  | EExtern of vvar * typ * exp
  | EHeapEnv of heapenvbinding list * exp
  (***** helpers *****)
  | EMacro of string * macro * exp
  | ETcFail of string * exp
  | EAsW of exp * world              (* used during type checking *)
  | ELoadSrc of string * exp         (* inserted/eliminated by parsing *)
  | ELoadedSrc of string * exp       (* placeholder to indicate source file *)

and value_ =
  | VBase of basevalue
  | VNull (* separate from basevalues to emphasize that it has-type Null *)
  | VVar of vvar
  | VEmpty
  | VExtend of value * value * value
  | VFun of pat * exp
  (* | VNewObjRef of int *)
  (***** abstract syntactic sugar *****)
  | VArray of typ * value list
  | VTuple of value list

and value = { pos: pos; value: value_ }

and basevalue =
  | Int of int
  | Str of string
  | Bool of bool
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
  (***** simple/uninterpreted predicates *****)
  | PEq of walue * walue
  | PApp of string * walue list
  (***** System !D uninterpreted predicates *****)
  | PHasTyp of hastyp
  | PHeapHas of heap * loc * walue
  (***** logical connectives *****)
  | PConn of string * formula list
  (***** quantifiers for dictionary expanding macros *****)
  | PAll of string * formula
  (***** abstract syntactic sugar *****)
  | PHas of walue * walue list
  | PDomEq of walue * walue list
  | PEqMod of walue * walue * walue list
  | PObjHas of walue list * walue * heap * loc

and hastyp = walue * typterm

and typ =
  | TRefinement of vvar * formula        (* {x|p} *)
  | TQuick of vvar * quicktyp * formula  (* {x:Q|p} *)
  | TBaseUnion of basetyp list           (* IntOrBool, NumOrStr, etc. *)
  | TMaybeNullRef of loc * formula       (* {v:Ref(l?)|p} *)
  | TNonNullRef of loc                   (* Ref(m!) *)

and prenextyp =
  | TExists of vvar * typ * prenextyp    (* Exists x:T. S *)
  | Typ of typ

and quicktyp =
  | QBase  of basetyp
  | QBoxes of typterm list
  | QRecd  of (string * typ) list * bool (* true if exact domain *)
  | QTuple of deptuple * bool            (* true if exact domain *)

and basetyp = BNum | BInt | BStr | BBool | BUndef

and uarrow = (tvars * lvars * hvars) * vvar * typ * heap * typ * heap

and deptuple = (vvar option * typ) list

and typterm =
  | UArrow of uarrow
  | UVar   of tvar
  | URef   of loc
  | UNull
  | UArray of typ
  | UMacro of vvar

and heapcell = (* [m |-> 0] [l |-> x:S] [l |-> (x:S, l')] *)
  | HWeak   of thawstate
  | HStrong of vvar option * typ * loc option (* TODO add closureinvariant *)

and heapbinding = loc * heapcell

and heap  = hvars * heapbinding list
and world = typ * heap
and frame = hvars * heap * world
and typs  = typ list
and heaps = heap list

and weakloc = loc * typ * loc (* m |-> (T, l) *)

and heapenvcell = (* [m |-> 0] [l |-> v] [l |-> (v,l')] *)
  | HEWeak   of thawstate
  | HEStrong of value * loc option * closureinvariant

and heapenvbinding = loc * heapenvcell

and heapenv = hvars * heapenvbinding list

and closureinvariant = typ option

and macro =
  | MacroT  of typ
  | MacroTT of typterm

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

type clause = formula * hastyp list

let wrapVal pos value = { pos = pos; value = value }

let lRoot = LocConst "lROOT"

let isWeakLoc = function LocConst(x) | LocVar(x) -> x.[0] = '~'
let isStrongLoc l = not (isWeakLoc l)

