
open Lang

(* started with ocamlbuild langUtils.inferred.mli *)

(******************************************************************************)

val spr : ('a, unit, string) format -> 'a
val fpr : out_channel -> ('a, out_channel, unit) format -> 'a

val (|>) : 'a -> ('a -> 'b) -> 'b

val pos0 : Lexing.position * Lexing.position

val freshVar : vvar -> vvar
val freshVarX : vvar -> vvar
val freshHVar : unit -> hvar

(******************************************************************************)

val mapTyp :
  ?fTyp:(typ -> typ) ->
  ?fForm:(formula -> formula) ->
  ?fTT:(typterm -> typterm) ->
  ?fWal:(walue -> walue) ->
  ?fVal:(value_ -> value_) ->
  ?fLoc:(loc -> loc) ->
  ?onlyTopForm:bool -> typ -> typ

val mapForm :
  ?fForm:(formula -> formula) ->
  ?fTT:(typterm -> typterm) ->
  ?fWal:(walue -> walue) ->
  ?fVal:(value_ -> value_) ->
  ?fLoc:(loc -> loc) ->
  ?onlyTopForm:bool -> formula -> formula

val mapHeap :
  ?fForm:(formula -> formula) ->
  ?fWal:(walue -> walue) ->
  ?fLoc:(loc -> loc) -> heap -> heap

val foldTyp :
  ?fForm:('a -> formula -> 'a) ->
  ?fTT:('a -> typterm -> 'a) ->
  ?fWal:('a -> walue -> 'a) -> 'a -> typ -> 'a

val mapExp : (exp -> exp) -> exp -> exp

val foldExp : ('a -> exp -> 'a) -> ('a -> value_ -> 'a) -> 'a -> exp -> 'a


(***** Helpers for Abstract Syntax Programming ********************************)

val tag : walue -> walue
val sel : walue -> walue -> walue
val upd : walue -> walue -> walue -> walue

val has : walue -> walue -> formula
val eqmod : walue -> walue -> walue list -> formula
val hastyp : walue -> typterm -> formula

val plus : walue -> walue -> walue
val minus : walue -> walue -> walue

val arrlen : walue -> walue

val lt : walue -> walue -> formula
val le : walue -> walue -> formula
val gt : walue -> walue -> formula
val ge : walue -> walue -> formula

val eq : walue -> walue -> formula

val packed : walue -> formula
val integer : walue -> formula

val vBool : bool -> value
val vStr : string -> value
val vInt : int -> value
val vNull : value
val vUndef : value
val vVar : vvar -> value
val vEmpty : value
val vBase : basevalue -> value
val vTup : value list -> value
(* val vNewObjRef : int -> value *)
val vFun : pat * exp -> value
val eFun : pat * exp -> exp

val wBool : bool -> walue
val wStr : string -> walue
val wInt : int -> walue
val wNull : walue
val theV : walue
val wVar : vvar -> walue
val wProj : int -> walue

val eVar : vvar -> exp
val eStr : string -> exp

val mkApp : exp -> exp list -> exp
val mkAppUn : value -> value list -> exp

val simplify : formula -> formula

val pNum : formula
val pBool : formula
val pStr : formula
val pDict : formula
val pGuard : value -> bool -> formula
val pTru : formula
val pFls : formula
val pAnd : formula list -> formula
val pOr : formula list -> formula
val pImp : formula -> formula -> formula
val pIff : formula -> formula -> formula
val pNot : formula -> formula
val pIte : formula -> formula -> formula -> formula
val pTruthy : walue -> formula
val pFalsy : walue -> formula
val pNonNull : walue -> formula
val pIsBang : walue -> typterm -> formula

val ty : formula -> typ
val tyAny : typ
val tyFls : typ
val tyInt : typ
val tyNum : typ
val tyBool : typ
val tyStr : typ
val tyDict : typ
val tyEmpty : typ

val tyNumOrBool : typ
val tyStrOrBool : typ
val tyIntOrBool : typ
val tyIntOrStr : typ
val tyNull : typ
val tyRef : loc -> typ
val tyUndef : typ
val tyNotUndef : typ
val tyArrDefault : typ
val tyArrayTuple : typ * typ list * bool -> typ
val tyTypTerm : typterm -> typ
val tyTupleNone : typ list -> typ
val tyTupleSome : (vvar option * typ) list -> typ
val tyTupleAll : (vvar * typ) list -> typ
val tyArray : typ -> formula -> typ

(***** Boxes ******************************************************************)

val idTypTerms : int ref * (int, typterm) Hashtbl.t * (typterm, int) Hashtbl.t

(***** Printers ***************************************************************)

val simpleSugarToTyp : (string * typ) list
val simpleSugarOfTyp : (typ * string) list
val strLoc : loc -> string
val strLocBinds : loc -> string
val strLocs : locs -> string
val strPat : pat -> string
val strThawState : thawstate -> string
val strBaseTyp : basetyp -> string
val strBaseValue : basevalue -> string
val strVal : value -> string
val strWal : walue -> string
val strTyp : typ -> string
val strPrenexTyp : prenextyp -> string
val strTT : typterm -> string
val strForm : formula -> string
val strFormExpanded : string -> formula list -> string
val strTTFlat : typterm -> string
val strHeap : ?arrowOutHeap:bool -> heap -> string
val strHeapCell : heapcell -> string
val strHeapEnvCell : heapenvcell -> string
val strHeapEnvBinding : heapenvbinding -> string
val strHeapBinding : heapbinding -> string
val strHeapEnv : heapenv -> string
val strWeakLoc : weakloc -> string
val strWorld : world -> string
val strFrame : frame -> string
val strBinding : vvar * typ -> string
val strCloInv : closureinvariant -> string

(***** Free variable computation **********************************************)

val freeVarsExp : exp -> VVars.t

(***** Type substitution ******************************************************)

type vsubst = (vvar * walue) list
type tsubst = (tvar * typ) list
type lsubst = (lvar * loc) list
type hsubst = (hvar * heap) list

module MasterSubst : sig
  type t = vsubst * tsubst * lsubst * hsubst
  val print : t -> unit
end

val substForm : MasterSubst.t -> formula -> formula
val substTyp  : MasterSubst.t -> typ     -> typ
val substHeap : MasterSubst.t -> heap    -> heap
val substWal  : MasterSubst.t -> walue   -> walue
val substLoc  : MasterSubst.t -> loc     -> loc
val substLocOpt  : MasterSubst.t -> loc option     -> loc option
val substPrenexTyp  : MasterSubst.t -> prenextyp -> prenextyp

val applyTyp : typ -> walue -> formula

(***** Expression substitution ************************************************)

val substVarInExp : vvar -> vvar -> exp -> exp

(***** Formula expansion and embedding ****************************************)

val expandPreTyp : typ -> typ
val expandPreHeap : heap -> heap
val embedForm : formula -> string
(* val embedForm : formula -> formula *)

(******************************************************************************)

val idSkolems : float Utils.IdTable.t

val isDepTuple : deptuple -> bool
val depTupleBinders : typ -> vvar list
val bindersOfDepTuple : deptuple -> vvar list

val newObjId : unit -> int

val valToSingleton : value -> typ
val valOfSingleton : string -> typ -> value
val maybeValOfSingleton : typ -> value option

val frozenNatives : heapbinding list
val frozenBxNatives : heapbinding list
val bxAbstractTypes : envbinding list

