open Prelude

type prefixOp =
  | PrefixLNot 
  | PrefixBNot 
  | PrefixPlus
  | PrefixMinus 
  | PrefixTypeof 
  | PrefixVoid 
  | PrefixDelete

type unaryAssignOp =
  | PrefixInc 
  | PrefixDec 
  | PostfixInc 
  | PostfixDec

type infixOp =
  | OpLT 
  | OpLEq 
  | OpGT 
  | OpGEq  
  | OpIn
  | OpInstanceof
  | OpEq
  | OpNEq
  | OpStrictEq
  | OpStrictNEq
  | OpLAnd
  | OpLOr 
  | OpMul
  | OpDiv
  | OpMod
  | OpSub
  | OpLShift
  | OpSpRShift
  | OpZfRShift
  | OpBAnd
  | OpBXor
  | OpBOr
  | OpAdd

type assignOp =
  | OpAssign
  | OpAssignAdd
  | OpAssignSub
  | OpAssignMul
  | OpAssignDiv
  | OpAssignMod
  | OpAssignLShift
  | OpAssignSpRShift
  | OpAssignZfRShift
  | OpAssignBAnd
  | OpAssignBXor
  | OpAssignBOr

type const =
  | CString of string
  | CRegexp of string * bool * bool
  | CNum of float
  | CInt of int
  | CBool of bool
  | CNull 
  | CUndefined

type prop =
  | PropId of id
  | PropString of string
  | PropNum of int

type varDecl =
  | VarDeclNoInit of pos * id
  | VarDecl of pos * id * expr
  | HintVarDecl of pos * string * id

and forInit =
  | NoForInit
  | VarForInit of varDecl list
  | ExprForInit of expr

and catch =
  | CatchClause of pos * id * stmt

and forInInit =
  | VarForInInit of pos * id
  | NoVarForInInit of pos * id

and caseClause =
  | CaseClause of pos * expr * stmt
  | CaseDefault of pos * stmt

and lvalue =
  | VarLValue of pos * id
  | DotLValue of pos * expr * id
  | BracketLValue of pos * expr * expr

and expr =
  | ConstExpr of pos * const
  | ArrayExpr of pos * expr list
  | ObjectExpr of pos * (pos * prop * expr) list
  | ThisExpr of pos
  | VarExpr of pos * id
  | DotExpr of pos * expr * id
  | BracketExpr of pos * expr * expr
  | NewExpr of pos * expr * expr list
  | PrefixExpr of pos * prefixOp * expr
  | UnaryAssignExpr of pos * unaryAssignOp * lvalue
  | InfixExpr of pos * infixOp * expr * expr
  | IfExpr of pos * expr * expr * expr
  | AssignExpr of pos * assignOp * lvalue * expr
  | ParenExpr of pos * expr
  | ListExpr of pos * expr * expr
  | CallExpr of pos * expr * expr list
  | FuncExpr of pos * id list * stmt
  | NamedFuncExpr of pos * id * id list * stmt
  | HintExpr of pos * string * expr

and stmt =
  | BlockStmt of pos * stmt list
  | EmptyStmt of pos  
  | ExprStmt of expr
  | IfStmt of pos * expr * stmt * stmt
  | IfSingleStmt of pos * expr * stmt
  | SwitchStmt of pos * expr * caseClause list
  | WhileStmt of pos * expr * stmt
  | DoWhileStmt of pos * stmt * expr
  | BreakStmt of pos
  | BreakToStmt of pos * id
  | ContinueStmt of pos
  | ContinueToStmt of pos * id
  | LabelledStmt of pos * id * stmt
  | ForInStmt of pos * forInInit * expr * stmt
  | ForStmt of pos * forInit * expr * expr * stmt
  | TryStmt of pos * stmt * catch list * stmt
  | ThrowStmt of pos * expr
  | ReturnStmt of pos * expr
  | WithStmt of expr * stmt
  | VarDeclStmt of pos * varDecl list
  | FuncStmt of pos * id * id list * stmt
  | HintStmt of pos * string * stmt

type prog =
  | Prog of pos * stmt list
