
open Lang

(* started with ocamlbuild langUtils.inferred.mli *)

(******************************************************************************)

val pos0 : Lexing.position * Lexing.position

val freshVar : vvar -> vvar
val freshHVar : unit -> hvar
(* val isTag : string -> bool *)

val terminate : unit -> 'a
val printBig : string -> string -> unit
val printErr : string -> string -> 'a
val printParseErr : string -> 'a
val printTcErr : string list -> 'a

(******************************************************************************)

val mapTyp :
  ?fForm:(formula -> formula) ->
  ?fTT:(typterm -> typterm) ->
  ?fWal:(walue -> walue) ->
  ?fVal:(value -> value) ->
  ?onlyTopForm:bool -> typ -> typ

val mapForm :
  ?fForm:(formula -> formula) ->
  ?fTT:(typterm -> typterm) ->
  ?fWal:(walue -> walue) ->
  ?fVal:(value -> value) ->
  ?onlyTopForm:bool -> formula -> formula

val foldTyp :
  ('a -> formula -> 'a) ->
  ('a -> typterm -> 'a) ->
  ('a -> walue -> 'a) -> 'a -> typ -> 'a

val foldForm : ('a -> formula -> 'a) -> 'a -> typ -> 'a

(* val foldTT : ('a -> typterm -> 'a) -> 'a -> typ -> 'a *)


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

val pNum : formula
val pBool : formula
val pStr : formula
val pDict : formula
val pGuard : value -> bool -> formula
val pAnd : formula list -> formula
val pOr : formula list -> formula
val pImp : formula -> formula -> formula
val pIff : formula -> formula -> formula
val pNot : formula -> formula
val pIte : formula -> formula -> formula -> formula
val pTruthy : walue -> formula
val pFalsy : walue -> formula

val ty : formula -> typ
val tyAny : typ
val tyFls : typ
val tyNum : typ
val tyBool : typ
val tyStr : typ
val tyDict : typ
val tyEmpty : typ
(* val tyIntOrBool : typ *)
(* val tyIntOrStr : typ *)
val tyStrOrBool : typ
(*
val tyArr : vvar -> typ -> typ -> typ
val tyNull : typ
*)
(* val tyArrImp : locs -> vvar -> typ -> heap -> typ -> heap -> typ *)
val tyRef : loc -> typ
val tySafeWeakRef : loc -> typ
val tyArrDefault : typ
val pIsBang : walue -> typterm -> formula
(*
val tyIsBang : walue -> typterm -> typ
*)
val tyArrayTuple : typ -> typ list -> bool -> typ

(***** Boxes ******************************************************************)

val idTypTerms : int ref * (int, typterm) Hashtbl.t * (typterm, int) Hashtbl.t

(***** Printers ***************************************************************)

val prettyConst : bool ref
val printFullUT : bool ref
val printFlatTyp : bool ref
val setPretty : bool -> unit
val sugarArrow : bool ref
val strLoc : loc -> string
val strLocs : locs -> string
val strBaseValue : basevalue -> string
val strValue : value -> string
val strWalue : walue -> string
val strTyp : typ -> string
val strTT : typterm -> string
val strForm : formula -> string
val strFormExpanded : string -> formula list -> string
val strTTFlat : typterm -> string
val strHeap : heap -> string
val strWorld : world -> string
val strFrame : frame -> string
val strBinding : vvar * typ -> string
val prettyStr : ('a -> 'b) -> 'a -> 'b
val prettyStrVal : value -> string
val prettyStrWal : walue -> string
val prettyStrForm : formula -> string
val prettyStrTyp : typ -> string
val prettyStrTT : typterm -> string
val prettyStrHeap : heap -> string

(***** Type substitution ******************************************************)

type vsubst = (vvar * walue) list
type tsubst = (tvar * typ) list
type lsubst = (hvar * loc) list
type hsubst = (hvar * heap) list

module MasterSubst : sig
  type t = vsubst * tsubst * lsubst * hsubst
end

val masterSubstForm : MasterSubst.t -> formula -> formula
val masterSubstTyp  : MasterSubst.t -> typ     -> typ
val masterSubstHeap : MasterSubst.t -> heap    -> heap

val applyTyp : typ -> walue -> formula

(***** Expression substitution ************************************************)

val substVarInExp : vvar -> vvar -> exp -> exp

(***** Formula expansion and embedding ****************************************)

val expandPreTyp : typ -> typ
val expandPreHeap : heap -> heap

val embedForm : formula -> formula

(******************************************************************************)

val idSkolems : float Utils.IdTable.t

