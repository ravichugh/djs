(** A simplified syntax for JavaScript. The primary simplification is
    that statements are eliminated. Expr{_ JS} is an expression-based syntax.

    We map JavaScript's statements to Expr{_ JS}'s control operators. Some
    statements map trivially to Expr{_ JS}. Others, such as switch and return,
    require less-obvious transformations. See the implementation for details.

    Expr{_ JS} has let-bindings [LetExpr]. We use let-bindings for some
    transformations. However, we do not transform [VarDeclStmt]s into
    let-bindings at this stage. Therefore, Expr{_ JS} uses both lexical scope
    and scope objects. *)
open Prelude

type expr
  = ConstExpr of pos * JavaScript_syntax.const
  | ArrayExpr of pos * expr list
  | ObjectExpr of pos * (pos * string * expr) list
      (** Object properties are transformed into string literals *)
  | ThisExpr of pos
  | VarExpr of pos * id (** identifiers bound in scope objects *)
  | IdExpr of pos * id (** let-bound identifiers *)
  | BracketExpr of pos * expr * expr
  | NewExpr of pos * expr * expr list
  | PrefixExpr of pos * id * expr
  | InfixExpr of pos * id * expr * expr
  | IfExpr of pos * expr * expr * expr
  | AssignExpr of pos * lvalue * expr
  | AppExpr of pos * expr * expr list
  | FuncExpr of pos * id list * expr
  | LetExpr of pos * id * expr * expr 
      (** We need let-expressions to simplify statements. *)
  | SeqExpr of pos * expr * expr
  | WhileExpr of pos * expr * expr
  | DoWhileExpr of pos * expr * expr
  | LabelledExpr of pos * id * expr
  | BreakExpr of pos * id * expr
  | ForInExpr of pos * id * expr * expr
  | VarDeclExpr of pos * id * expr
      (** We do not transform VarDeclStmts to let-bindings at this stage *)
  | TryCatchExpr of pos * expr * id * expr
  | TryFinallyExpr of pos * expr * expr
  | ThrowExpr of pos * expr
  | FuncStmtExpr of pos * id * id list * expr
      (** We leave function statements in place, so that they can be lifted
          for JavaScript to turned into letrecs for Typed JavaScript. *)
  | HintExpr of pos * string * expr


and lvalue =
    VarLValue of pos * id
  | PropLValue of pos * expr * expr

val from_javascript : JavaScript_syntax.prog -> expr

val from_javascript_expr : JavaScript_syntax.expr -> expr

(** locally defined functions. *)
val locals : expr -> IdSet.t
