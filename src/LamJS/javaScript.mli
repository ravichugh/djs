open Prelude
open JavaScript_syntax

val parse_javascript : string -> string -> prog
val parse_javascript_from_channel : in_channel -> string -> prog
val parse_expr : string -> string -> expr

module Pretty : sig

  open Format
  open FormatExt

  val p_const : const -> printer
  val p_expr : expr -> printer
  val p_stmt : stmt -> printer
  val p_prog : prog -> printer
  val p_infixOp : infixOp -> printer
  val p_prefixOp : prefixOp -> printer
end
