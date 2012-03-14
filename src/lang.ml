
let pr = Printf.printf
let spr = Printf.sprintf
let fpr = Printf.fprintf

let (|>) f x = x f


(*****************************************************************************)

exception Parse_error of string
exception Z3_read_error of string
exception Tc_error of string list

let err s = raise (Tc_error s)
let z3err s = raise (Z3_read_error s)
let kill s = fpr stderr "\nFATAL ERROR\n\n%s\n" s; exit 1

(* for current nesting during type checking *)
let depth = ref 0
let indent () = String.make (2 * !depth) ' '
let bigindent () = String.make (4 * !depth) ' '


(*****************************************************************************)

type tag = string

let tagDict  = "Dict"      (* for internal functional dictionaries *)
let tagRef   = "Ref"       (* for internal references *)
let tagArray = "Array"     (* for internal functional arrays *)
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
  | EVal of value (* these get created by ANFer, not the parser *)
  | EBase of basevalue
  | EVar of vvar
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
  | EFreeze of loc * exp
  | EThaw of loc * exp
  | ERefreeze of loc * exp
  (* TODO rename to EWeak, define weak constraint list instead of heap *)
  | EHeap of heap * exp   (* using this to add weak constraints *)
  (***** control operators *****)
  | ELabel of lbl * frame option * exp (* TODO get rid of annotation? *)
  | EBreak of lbl * exp
  | EThrow of exp
  | ETryCatch of exp * vvar * exp
  | ETryFinally of exp * exp
  (***** create a proto-based object or array *****)
  | ENewObj of exp * loc * exp * loc
  (***** helpers for parsing *****)
  | ELoadSrc of string * exp         (* inserted/eliminated by parsing *)
  | ELoadedSrc of string * exp       (* placeholder to indicate source file *)

and value =
  | VBase of basevalue
  | VVar of vvar
  | VEmpty
  | VExtend of value * value * value
  | VArray of typ * value list (* TODO okay to drop typ? *)
  | VFun of (tvars * lvars * hvars) * vvar * (typ * heap) option * exp

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
  | PUn of unpred
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

(* TODO inline this into above type *)
and unpred = (* uninterpreted System D predicates *)
  | HasTyp of walue * typterm

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

and uarr = (tvars * lvars * hvars) * vvar * typ * heap * typ * heap

and typterm =
  | UArr  of uarr
  | UVar  of tvar
  | URef  of loc
  | UNull
  | UArray of typ

and heapconstraint =
  | HConc    of vvar * typ       (* [l |-> x:S] *)
  | HConcObj of vvar * typ * loc (* [l |-> (x:S, l')] *)
  | HWeakObj of thawstate * typ * loc (* [l |-> (0, S, l')] *)

and heap  = hvar list * (loc * heapconstraint) list
and world = typ * heap
and frame = hvars * heap * world
and typs  = typ list
and heaps = heap list

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

type env = envbinding list

type clause = formula * unpred list

module TypeTerms =
  Set.Make (struct type t = typterm let compare = compare end)

let mkTypeTerms l =
  List.fold_left (fun acc ut -> TypeTerms.add ut acc) TypeTerms.empty l

(* TODO *)
let botHeapConstraints = [(LocConst "blubber", HConc ("dummyHAbs", TBot))]
let botHeap = ([], botHeapConstraints)
let botSubst = [("dummySubst", WVal (VVar "blah"))]

let lRoot = LocConst "lROOT"
let lObjectPro = LocConst "lObjectProto"

let isWeakLoc = function LocConst(x) | LocVar(x) -> x.[0] = '~'
let isStrongLoc l = not (isWeakLoc l)

