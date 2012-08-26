
{
open LangParser

}

let letter  = ['A'-'Z''a'-'z''_']
let digit   = ['0'-'9']
(* let ident   = ['a'-'z''_'] (letter|digit)* *)
(* let ident   = ['a'-'z''_'] (letter|digit|''')* *)
let ident   = ['a'-'z''_''&'] (letter|digit|''')*
let tyvar   = ['A'-'Z'] (letter|digit)*
let white   = [' ' '\t' '\r']
let newline = ['\n']
let hashk   = '#' (letter|digit)+

let str =
  (letter
    | digit
    | [' ' '+' '-' '*' '/' '=' '(' ')' '&' '|' '.' ',' '{' '}' ';'])*


rule token = parse
  | eof { EOF }

  (* NOTE: keep these in sync with LangUtils.simpleSugarToTyp *)
  | "Int"        { SUGAR "Int" }
  | "Bool"       { SUGAR "Bool" }
  | "Str"        { SUGAR "Str" }
  | "Dict"       { SUGAR "Dict" }
  | "Top"        { SUGAR "Top" }
  | "Bot"        { SUGAR "Bot" }
  | "Num"        { SUGAR "Num" }
  | "Empty"      { SUGAR "Empty" }
  | "Undef"      { SUGAR "Undef" }
  | "NotUndef"   { SUGAR "NotUndef" }
  | "NumOrBool"  { SUGAR "NumOrBool" }
  | "IntOrBool"  { SUGAR "IntOrBool" }
  | "IntOrStr"   { SUGAR "IntOrStr" }
  | "StrOrBool"  { SUGAR "StrOrBool" }
(*
  | "EXTEND"       { SUGAR_EXTEND }
  | "FLD"          { SUGAR_FLD }
*)
  | "type"         { TYPE }
  | "weak"         { HEAP }
  | "ref"          { NEWREF }
  | "Ref"          { REFTYPE }
  | "Arr"          { ARRTYPE }
  | "same"         { SAME }
  | "sameType"     { SAME_TYPE }
  | "sameExact"    { SAME_EXACT }
  (* | "fold"         { FOLD } *)
  (* | "unfold"       { UNFOLD } *)
  | "frzn"         { FRZN }
  | "thwd"         { THWD }
  | "freeze"       { FREEZE }
  | "thaw"         { THAW }
  (* | "refreeze"     { REFREEZE } *)
  | "break"        { BREAK }
  | "throw"        { THROW }
  | "try"          { TRY }
  | "catch"        { CATCH }
  | "finally"      { FINALLY }
  | "val"          { EXTERN }
  | "fail"         { FAIL }
  (* | "List"         { LIST } *)
  (* | "True"         { VBOOL true } *)
  (* | "False"        { VBOOL false } *)
  (* | "true"         { BOOL true } *)
  (* | "false"        { BOOL false } *)
  | "true"         { VBOOL true }
  | "false"        { VBOOL false }
  | "TRU"          { BOOL true }
  | "FLS"          { BOOL false }
  | "let"          { LET }
  | "rec"          { REC }
  | "not"          { NOT }
  | "and"          { AND }
  | "or"           { OR }
  | "implies"      { IMP }
  | "iff"          { IFF }
  | "ite"          { ITE }
  | "="            { EQ }
  | "in"           { IN }
  | "as"           { AS }
  | "fun"          { FUN }
  | "|->"          { MAPSTO }
  | "->"           { ARROW }
  | "if"           { IF }
  | "then"         { THEN }
  | "else"         { ELSE }
  | "with"         { WITH }
  | "begin"        { BEGIN }
  | "end"          { END }
  | "tag"          { TAG }
  | "has"          { HAS }
  | "sel"          { SEL }
  | "empty"        { EMPTY }
  | "upd"          { UPD }
  | "eqmod"        { EQMOD }
  | "dom"          { DOM }
  | "bot"          { WBOT }
  | "heaphas"      { HEAPHAS }
  | "heapsel"      { HEAPSEL }
  | "objhas"       { OBJHAS }
  | "objsel"       { OBJSEL }
  | "packed"       { PACKED }
  | "len"          { LEN }
  | "truthy"       { TRUTHY }
  | "falsy"        { FALSY }
  | "integer"      { INTEGER }
  (* | "ctor"         { CTOR } *)
  (* | "All"          { ALL } *)
  (* | "all"          { LOCALL } *)
  | "new"          { NEW }
  (* | "nil"          { NIL } *)
  | "null"         { NULL }
  | "Null"         { NULLBOX }
  | "undefined"    { UNDEF }
  | "!"            { BANG }
  | "?"            { QMARK }
  (* | ">>"           { GTGT } *)
  | "<="           { LE }
  | ">="           { GE }
  (* | "!="           { NE } *)
  (* | "=="           { EQEQ } *)
  (* | "&&"           { AMPAMP } *)
  (* | "||"           { PIPEPIPE } *)
  | "..."          { ELLIPSIS }
  | ":::"          { TCOLON }
  | "::"           { DCOLON }
  | ":="           { ASSGN }
  | "++"           { PLUSPLUS }
  | "+"            { PLUS }
  | "-"            { MINUS }
  | "*"            { MUL }
  | "/"            { DIV }
  | "<"            { LT }
  | ">"            { GT } (* ordering issue with >>? *)
  | "[["           { LTUP }
  | "]]"           { RTUP }
  | "("            { LPAREN }
  | ")"            { RPAREN }
  | "["            { LBRACK }
  | "]"            { RBRACK }
  | "{"            { LBRACE }
  | "}"            { RBRACE }
  | "."            { DOT }
  | ","            { COMMA }
  | ";"            { SEMI }
  | ":"            { COLON }
  | "|"            { PIPE }
  (* | "@"            { AT } *)
  (* | "#"            { HASH } *)
  | "_"            { UNDERSCORE }

  | digit+ as s         { INT (int_of_string s) }
  (* | ident as s          { VAR s } *)
  | ident as s          { let s = Str.global_replace (Str.regexp "'") "_prime" s
                          in VAR s }
  | tyvar as s          { TVAR s }
  | ('~'ident) as s     { VAR s }
  | ('~'tyvar) as s     { TVAR s }
  | hashk as s          { LBL (String.sub s 1 (String.length s - 1)) }
  | '"' (str as s) '"'  { STR s}

  | white       { token lexbuf }
  | newline     { Lexing.new_line lexbuf; token lexbuf }

  | "(*"		    { comments 0 lexbuf }

  | _  { raise (Failure ("Lex: bad char ["^(Lexing.lexeme lexbuf)^"]")) }

and comments level = parse
  | "*)"	{ if level = 0 then token lexbuf else comments (level-1) lexbuf }
  | "(*"	{ comments (level+1) lexbuf }
  | newline     { Lexing.new_line lexbuf; comments level lexbuf }
  | _	  	{ comments level lexbuf }
  | eof		{ Printf.printf "comments are not closed\n"; raise End_of_file }

