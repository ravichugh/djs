open Prelude
open FormatExt

type op1 = 
  | Op1Prefix of id
  | Deref
  | Ref
  | Prim1 of string

(* TODO: unchecked operations should always use differnet syntax. add an
   uncheckedGetField, uncheckedSetField, updateField, App, and if, ? *)
type op2 =
  | Op2Infix of id
  | Prim2 of string
  | GetField
  | UnsafeGetField
  | DeleteField
  | SetRef

(** NOTE: reference and object manipulation are defined using [EOp1] and 
    [EOp2]. This design shrinks the size of many cases. *)
type exp =
  | EConst of pos * JavaScript_syntax.const
  | EId of pos * id
  | EObject of pos * (pos * string * exp) list
  | EUpdateField of pos * exp * exp * exp
  | EOp1 of pos * op1 * exp
  | EOp2 of pos * op2 * exp * exp
  | EIf of pos * exp * exp * exp
  | EApp of pos * exp * exp list
  | ESeq of pos * exp * exp
  | ELet of pos * id * exp * exp
  | EFix of pos * (id * exp) list * exp 
      (** All bindings must be [ELambda]s. *)
  | ELabel of pos * id * exp
  | EBreak of pos * id * exp
  | ETryCatch of pos * exp * exp
      (** Catch block must be an [ELambda] *)
  | ETryFinally of pos * exp * exp
  | EThrow of pos * exp
  | ELambda of pos * id list * exp

val desugar : Exprjs_syntax.expr -> exp

module Pretty : sig
  val p_op1 : op1 -> printer
  val p_op2 : op2 -> printer
  val p_exp : exp -> printer
end 

val fv : exp -> IdSet.t
val rename : id -> id -> exp -> exp
val operators : exp -> IdSet.t
