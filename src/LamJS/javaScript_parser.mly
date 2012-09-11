(*****************************************************************************)
(*  Original: LambdaJS                                                       *)
(*  Modified: Ravi Chugh (rkc) (rchugh@cs.ucsd.edu)                          *)
(*****************************************************************************)

%{
(** A JavaScript parser that does not do semicolon insertion. *)
open Prelude
open JavaScript_syntax

exception Expected_lvalue

exception Parse_failure of string

let rec expr_to_lvalue (e : expr) : lvalue =  match e with
  | VarExpr (p,x) -> VarLValue (p,x)
  | DotExpr (p,e,x) -> DotLValue (p,e,x)
  | BracketExpr (p,e1,e2) -> BracketLValue (p,e1,e2)
  | ParenExpr (_, e) -> expr_to_lvalue e
  | _ -> raise Expected_lvalue
%}

%token <string> ContinueId
%token <string> BreakId
%token <string> Id
%token <string> String
%token <string * bool * bool> Regexp
%token <int> Int
%token <float> Float
%token <JavaScript_syntax.assignOp> AssignOp

%token <string> HINT

%token If Else True False New Instanceof This Null Function Typeof Void
 Delete Switch Default Case While Do Break Var In For Try Catch Finally Throw
 Return With Continue

%token LBrace RBrace LParen RParen Assign
 Semi Comma Ques Colon LOr LAnd BOr BXor BAnd StrictEq AbstractEq
 StrictNEq AbstractNEq LShift RShift SpRShift LEq LT GEq GT PlusPlus MinusMinus
 Plus Minus Times Div Mod Exclamation Tilde Period LBrack RBrack

%token EOF

(* http://stackoverflow.com/questions/1737460/
   how-to-find-shift-reduce-conflict-in-this-yacc-file *)
%nonassoc GreaterThanColon
%nonassoc Colon
%nonassoc LowerThanElse
%nonassoc Else

%left LOr
%left LAnd
%left BOr
%left BXor
%left BAnd
%left StrictEq StrictNEq AbstractEq AbstractNEq
%left LT LEq GT GEq In Instanceof
%left LShift RShift SpRShift
%left Plus Minus
%left Times Div Mod


%start program
%start expression

%type <JavaScript_syntax.prog> program
%type <JavaScript_syntax.expr> expression

%%

exprs
  : { [] }
  | assign_expr { [$1] }
  | assign_expr Comma exprs { $1::$3 }

stmts
  : { [] }
  | stmt stmts { $1 :: $2 }

cases
  : { [] }
  | case cases { $1 :: $2 }

catches
  : { [] }
  | catch catches { $1 :: $2 }

ids
  : { [] }
  | Id { [$1] }
  | Id Comma ids { $1 :: $3 }

prop
  : Id { PropId $1 }  %prec GreaterThanColon
  | String { PropString $1 }

fields
  : { [] }
  | prop Colon expr 
    { [ (($startpos($1), $startpos($3)), $1, $3) ] }
  | prop Colon expr Comma fields  
      { (($startpos($1), $startpos($3)), $1, $3) :: $5 }

varDecls
  : varDecl { [$1] }
  | varDecl Comma varDecls { $1::$3 }

varDecls_noin
  : varDecl_noin { [$1] }
  | varDecl_noin Comma varDecls_noin { $1::$3 } 

element_list
  : 
      { [] }
  | Comma 
      { [ ConstExpr (($startpos, $endpos), CUndefined) ] }
  | assign_expr { [$1] }
  | assign_expr Comma element_list 
      { $1::$3 }

const :
  | True { CBool true }
  | False { CBool false }
  | Null { CNull }
  | String { CString $1 }
  | Regexp { let re, g, ci = $1 in  CRegexp (re, g, ci) }
  | Int { CInt $1}
  | Float { CNum $1 }

primary_expr :
  | const { ConstExpr (($startpos, $endpos), $1) }
  | Id { VarExpr (($startpos, $endpos), $1) }
  | LBrack element_list RBrack
      { ArrayExpr (($startpos, $endpos),$2) }
  | LBrace fields RBrace
      { ObjectExpr (($startpos, $endpos),$2) }
  | LParen expr RParen
      { ParenExpr (($startpos, $endpos),$2) }
  | HINT primary_expr { HintExpr (($startpos, $endpos), $1, $2) }
  | This { ThisExpr (($startpos, $endpos)) }

member_expr
  : primary_expr 
      { $1 }
  | Function LParen ids RParen LBrace src_elts RBrace
    { FuncExpr (($startpos, $endpos), $3, 
                BlockStmt (($startpos($5), $endpos($7)), $6)) }
  | Function LParen ids RParen HINT LBrace src_elts RBrace
      { HintExpr 
          (($startpos($5), $endpos($5)), $5,
           FuncExpr (($startpos, $endpos), $3, 
                     BlockStmt (($startpos($6), $endpos($8)), $7))) }
  | Function Id LParen ids RParen LBrace src_elts RBrace
      { NamedFuncExpr (($startpos, $endpos), $2, $4, 
                       BlockStmt (($startpos($6), $startpos($8)), $7)) }
  (* rkc: adding hints around this form for recursive functions *)
  | Function Id LParen ids RParen HINT LBrace src_elts RBrace
      { HintExpr
          (($startpos($6), $endpos($6)), $6,
           NamedFuncExpr (($startpos, $endpos), $2, $4, 
                       BlockStmt (($startpos($7), $startpos($9)), $8))) }
  | member_expr Period Id
      { DotExpr (($startpos, $endpos), $1, $3) } 
  | member_expr LBrack expr RBrack
      { BracketExpr (($startpos, $endpos),$1,$3) }
  | New member_expr LParen exprs RParen 
      { NewExpr (($startpos, $endpos),$2,$4) }
  
new_expr
  : member_expr
      { $1 }
  | New new_expr
      { NewExpr (($startpos, $endpos),$2,[]) }


call_expr
  : member_expr LParen exprs RParen
      { CallExpr (($startpos, $endpos),$1,$3) }
  | call_expr LParen exprs RParen
      { CallExpr (($startpos, $endpos),$1,$3) }
  | call_expr LBrack expr RBrack 
      { BracketExpr (($startpos, $endpos),$1,$3) }
  | call_expr Period Id 
      { DotExpr (($startpos, $endpos), $1, $3) }

lhs_expr
  : new_expr
      { $1 }
  | call_expr 
      { $1 }

postfix_expr
  : lhs_expr 
      { $1 }
  | lhs_expr PlusPlus
      { UnaryAssignExpr (($startpos, $endpos),PostfixInc,expr_to_lvalue $1) }
  | lhs_expr MinusMinus
      { UnaryAssignExpr (($startpos, $endpos),PostfixDec,expr_to_lvalue $1) }

unary_expr
  : postfix_expr 
      { $1 }
  | PlusPlus unary_expr 
      { UnaryAssignExpr (($startpos, $endpos),PrefixInc,expr_to_lvalue $2) }
  | MinusMinus unary_expr 
      { UnaryAssignExpr (($startpos, $endpos),PrefixDec,expr_to_lvalue $2) }
  | Exclamation unary_expr 
      { PrefixExpr (($startpos, $endpos),PrefixLNot,$2) } 
  | Tilde unary_expr 
      { PrefixExpr (($startpos, $endpos),PrefixBNot,$2) }
  | Minus unary_expr
      { PrefixExpr (($startpos, $endpos),PrefixMinus,$2) }
  | Plus unary_expr
      { PrefixExpr (($startpos, $endpos),PrefixPlus,$2) }
  | Typeof unary_expr
      { PrefixExpr (($startpos, $endpos),PrefixTypeof,$2) }
  | Void unary_expr
      { PrefixExpr (($startpos, $endpos),PrefixVoid,$2) }
  | Delete unary_expr 
      { PrefixExpr (($startpos, $endpos),PrefixDelete,$2) }

(* Combines UnaryExpression, MultiplicativeExpression, AdditiveExpression, and
   ShiftExpression by using precedence and associativity rules. *)
op_expr
  : unary_expr { $1 }
  | op_expr Times op_expr
      { InfixExpr (($startpos, $endpos),OpMul,$1,$3) }
  | op_expr Div op_expr
      { InfixExpr (($startpos, $endpos),OpDiv,$1,$3) }
  | op_expr Mod op_expr 
      { InfixExpr (($startpos, $endpos),OpMod,$1,$3) }
  | op_expr Plus op_expr
      { InfixExpr (($startpos, $endpos),OpAdd,$1,$3) }
  | op_expr Minus op_expr
      { InfixExpr (($startpos, $endpos),OpSub,$1,$3) }
  | op_expr LShift op_expr 
      { InfixExpr (($startpos, $endpos),OpLShift,$1,$3) }
  | op_expr RShift op_expr
      { InfixExpr (($startpos, $endpos),OpZfRShift,$1,$3) }
  | op_expr SpRShift op_expr
      { InfixExpr (($startpos, $endpos),OpSpRShift,$1,$3) }

in_expr
  : op_expr 
      { $1 }
  | in_expr LT in_expr
      { InfixExpr (($startpos, $endpos),OpLT,$1,$3) }
  | in_expr GT in_expr 
      { InfixExpr (($startpos, $endpos),OpGT,$1,$3) }
  | in_expr LEq in_expr 
      { InfixExpr (($startpos, $endpos),OpLEq,$1,$3) }
  | in_expr GEq in_expr
      { InfixExpr (($startpos, $endpos),OpGEq,$1,$3) }
  | in_expr Instanceof in_expr
      { InfixExpr (($startpos, $endpos),OpInstanceof,$1,$3) }
  | in_expr In in_expr
      { InfixExpr (($startpos, $endpos),OpIn,$1,$3) }
  | in_expr StrictEq in_expr 
      { InfixExpr (($startpos, $endpos),OpStrictEq,$1,$3) }
  | in_expr StrictNEq in_expr
      { InfixExpr (($startpos, $endpos),OpStrictNEq,$1,$3) }
  | in_expr AbstractEq in_expr
      { InfixExpr (($startpos, $endpos),OpEq,$1,$3) }
  | in_expr AbstractNEq in_expr
      { InfixExpr (($startpos, $endpos),OpNEq,$1,$3) }
  | in_expr BAnd in_expr
      { InfixExpr (($startpos, $endpos),OpBAnd,$1,$3) }
  | in_expr BXor in_expr
      { InfixExpr (($startpos, $endpos),OpBXor,$1,$3) }
  | in_expr BOr in_expr
      { InfixExpr (($startpos, $endpos),OpBOr,$1,$3) }
  | in_expr LAnd in_expr
      { InfixExpr (($startpos, $endpos),OpLAnd,$1,$3) }
  | in_expr LOr in_expr
      { InfixExpr (($startpos, $endpos),OpLOr,$1,$3) }

cond_expr
  : in_expr
      { $1 }
  | in_expr Ques assign_expr Colon assign_expr 
      { IfExpr (($startpos, $endpos),$1,$3,$5) }


assign_expr
  : cond_expr
      { $1 }
  (* we need the use Assign (token for =) in other productions. *)
  | lhs_expr AssignOp assign_expr 
    { AssignExpr (($startpos, $endpos), $2, expr_to_lvalue $1, $3) }
  | lhs_expr Assign assign_expr 
    { AssignExpr (($startpos, $endpos), OpAssign, expr_to_lvalue $1, $3) }


expr 
  : assign_expr 
      { $1 }
  | expr Comma assign_expr
      { ListExpr (($startpos, $endpos),$1,$3) }

noin_expr
  : op_expr
      { $1 }
  | noin_expr LT noin_expr 
      { InfixExpr (($startpos, $endpos),OpLT,$1,$3) }
  | noin_expr GT noin_expr
      { InfixExpr (($startpos, $endpos),OpGT,$1,$3) }
  | noin_expr LEq noin_expr
      { InfixExpr (($startpos, $endpos),OpLEq,$1,$3) }
  | noin_expr GEq noin_expr
      { InfixExpr (($startpos, $endpos),OpGEq,$1,$3) }
  | noin_expr Instanceof noin_expr
      { InfixExpr (($startpos, $endpos),OpInstanceof,$1,$3) }
  | noin_expr StrictEq noin_expr 
      { InfixExpr (($startpos, $endpos),OpStrictEq,$1,$3) }
  | noin_expr StrictNEq noin_expr
      { InfixExpr (($startpos, $endpos),OpStrictNEq,$1,$3) }
  | noin_expr AbstractEq noin_expr
      { InfixExpr (($startpos, $endpos),OpEq,$1,$3) }
  | noin_expr AbstractNEq noin_expr
      { InfixExpr (($startpos, $endpos),OpNEq,$1,$3) }
  | noin_expr BAnd noin_expr 
      { InfixExpr (($startpos, $endpos),OpBAnd,$1,$3) }
  | noin_expr BXor noin_expr 
      { InfixExpr (($startpos, $endpos),OpBXor,$1,$3) }
  | noin_expr BOr noin_expr
      { InfixExpr (($startpos, $endpos),OpBOr,$1,$3) }
  | noin_expr LAnd noin_expr
      { InfixExpr (($startpos, $endpos),OpLAnd,$1,$3) }
  | noin_expr LOr noin_expr 
      { InfixExpr (($startpos, $endpos),OpLOr,$1,$3) }

cond_noin_expr
  : noin_expr { $1 }
  | noin_expr Ques assign_noin_expr Colon assign_noin_expr 
    { IfExpr (($startpos, $endpos),$1,$3,$5) }

assign_noin_expr
  : cond_noin_expr { $1 }
  | lhs_expr AssignOp assign_noin_expr 
    { AssignExpr (($startpos, $endpos), $2, expr_to_lvalue $1, $3) }
  | lhs_expr Assign assign_noin_expr 
    { AssignExpr (($startpos, $endpos), OpAssign, expr_to_lvalue $1, $3) }

expr_noin
  : assign_noin_expr { $1 }
  | noin_expr Comma assign_noin_expr 
      { ListExpr (($startpos, $endpos),$1,$3) }

varDecl
  : Id { VarDeclNoInit (($startpos, $endpos),$1) }
  | Id Assign assign_expr { VarDecl (($startpos, $endpos),$1,$3) }
  | Id HINT { HintVarDecl (($startpos, $endpos), $2, $1) }
  (* rkc: added to support var x /*: T */ = e *)
  | Id HINT Assign assign_expr
      { HintVarDeclInit (($startpos, $endpos), $2, $1, $4) }

varDecl_noin
  : Id { VarDeclNoInit (($startpos, $endpos),$1) }
  | Id Assign assign_noin_expr { VarDecl (($startpos, $endpos),$1,$3) }
  | Id HINT { HintVarDecl (($startpos, $endpos), $2, $1) }
  (* rkc: added to support for (var i /*: T */ = e; ...; ...) *)
  | Id HINT Assign assign_expr
      { HintVarDeclInit (($startpos, $endpos), $2, $1, $4) }

case
  : Case expr Colon stmts 
  { CaseClause (($startpos, $endpos),$2,BlockStmt (($startpos, $endpos),$4)) }
  | Default Colon stmts
  { CaseDefault (($startpos, $endpos),BlockStmt (($startpos, $endpos),$3)) }

forInInit :
  | Id 
      { NoVarForInInit (($startpos, $endpos), $1) }
  | Var Id 
      { VarForInInit (($startpos, $endpos), $2) }

forInit
  : { NoForInit }
  | Var varDecls_noin { VarForInit $2 }
  | expr_noin { ExprForInit $1 }

catch
  : Catch LParen Id RParen block
    { CatchClause (($startpos, $endpos), $3, $5) }


block : LBrace stmts RBrace
      { BlockStmt (($startpos, $endpos),$2) }

paren_expr : LParen expr RParen
      { ParenExpr (($startpos, $endpos),$2) }

opt_expr :
  | { ConstExpr (($startpos, $endpos), CUndefined) }
  | expr { $1 }

stmt : 
  | LBrace stmts RBrace
      { BlockStmt (($startpos, $endpos), $2) }
  | Semi 
      { EmptyStmt (($startpos, $endpos)) }
  | expr Semi
      { ExprStmt $1 }
  | Continue Semi 
      { ContinueStmt (($startpos, $endpos)) }
  | ContinueId Semi 
      { ContinueToStmt (($startpos, $endpos),$1) }
  | If LParen expr  RParen stmt  %prec LowerThanElse
    { IfSingleStmt (($startpos, $endpos), $3, $5) }
  | If LParen expr RParen stmt Else stmt
    { IfStmt (($startpos, $endpos), $3, $5, $7) }

  | Switch paren_expr LBrace cases RBrace 
      { SwitchStmt (($startpos, $endpos),$2,$4) }
  | While paren_expr stmt
      { WhileStmt (($startpos, $endpos),$2,$3) }
  | Do block While paren_expr Semi
      { DoWhileStmt (($startpos, $endpos),$2,$4) }

  (* rkc: adding hints around while, do/while, and for statements *)
  | HINT While paren_expr stmt
      { HintStmt (($startpos, $endpos), $1,
                  WhileStmt (($startpos, $endpos),$3,$4)) }
  | HINT Do block While paren_expr Semi
      { HintStmt (($startpos, $endpos), $1,
                  DoWhileStmt (($startpos, $endpos),$3,$5)) }
  | HINT For LParen forInit Semi opt_expr Semi opt_expr RParen stmt
      { HintStmt (($startpos, $endpos), $1,
                  ForStmt (($startpos, $endpos),$4,$6,$8,$10)) }

  (* rkc 3/31 *)
  | HINT For LParen forInInit In expr RParen stmt
      { HintStmt (($startpos, $endpos), $1,
                  ForInStmt (($startpos, $endpos),$4,$6,$8)) }

  | Break  Semi
      { BreakStmt (($startpos, $endpos)) }
  | BreakId Semi
      { BreakToStmt (($startpos, $endpos),$1) }
  | Id Colon stmt { LabelledStmt (($startpos, $endpos), $1, $3) }
  | For LParen forInInit In expr RParen stmt
    { ForInStmt (($startpos, $endpos),$3,$5,$7) }
  | For LParen forInit Semi opt_expr Semi opt_expr RParen stmt
    { ForStmt (($startpos, $endpos),$3,$5,$7,$9) }
  | Try block catches
    { TryStmt (($startpos, $endpos),$2,$3,EmptyStmt (($startpos, $endpos))) }
  | Try block catches Finally block { TryStmt (($startpos, $endpos),$2,$3,$5) }
  | Throw expr Semi 
      { ThrowStmt (($startpos, $endpos),$2) }
  | Return Semi 
      { ReturnStmt (($startpos, $endpos),
                    ConstExpr (($startpos, $endpos), CUndefined)) }
  | Return expr Semi 
      { ReturnStmt (($startpos, $endpos),$2) } 
  | Var varDecls Semi
      { VarDeclStmt (($startpos, $endpos),$2) }
  | With LParen expr RParen stmt
      { WithStmt ($3, $5) }

src_elt_block
  : LBrace src_elts RBrace 
      { BlockStmt (($startpos, $endpos),$2) }
 
src_elts
  : { [] }
  | src_elt src_elts { $1::$2 }

src_elt
  : stmt { $1 }
  | Function Id LParen ids RParen src_elt_block
    { FuncStmt (($startpos, $endpos), $2, $4, $6) } 
  | Function Id LParen ids RParen HINT src_elt_block
    { HintStmt (($startpos($6), $endpos($6)), $6,
                FuncStmt (($startpos, $endpos), $2, $4, $7)) } 

program : src_elts EOF { Prog (($startpos, $endpos), $1) }

expression : expr EOF { $1 }

%%
