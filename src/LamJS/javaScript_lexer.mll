{
open Prelude
open Lexing
open JavaScript_parser
open JavaScript_syntax

module S = String

let parse_re = ref false

(* TODO: if integer conversions overflow, treat as a float *)
let parse_num_lit (s : string) : token =
  if S.contains s 'x' || S.contains s 'X'
    then Int (int_of_string s)
    else if S.contains s '.'
           then Float (float_of_string s)
           else if S.contains s 'e' || S.contains s 'E'
                  then Float (float_of_string s)
                  else Int (int_of_string s)

let mk_loc (buf : lexbuf) : pos =
  Lexing.lexeme_start_p buf, Lexing.lexeme_end_p buf

let block_comment_buf = Buffer.create 120

let string_buf = Buffer.create 100

let comment_start_p = ref dummy_pos

let get_string () = 
  let s = Buffer.contents string_buf in
    Buffer.clear string_buf;
    s
}

(* dec_digit+ corresponds to DecimalDigits in the spec. *)
let dec_digit = ['0'-'9']

let signed_int = dec_digit+ | ('+' dec_digit+) | ('-' dec_digit+)

let expt_part = ['e' 'E'] signed_int

let dec_int_lit = '0' | (['1'-'9'] dec_digit*)

let hex = ['0'-'9' 'A'-'F' 'a'-'f']

let hex_lit = ("0x" | "0X") hex+

let dec_lit = 
  (dec_int_lit '.' dec_digit* expt_part?) | 
  ('.' dec_digit+ expt_part?) |
  (dec_int_lit expt_part?)

let num_lit = dec_lit | hex_lit

let ident = ['a'-'z' 'A'-'Z' '$' '_']['a'-'z' 'A'-'Z' '0'-'9' '$' '_']*

let digit = ['0'-'9']

let char = [^ '"' '\\']

let blank = [ ' ' '\t' ]

let escape_sequence
  = [^ '\r' '\n'] | ('x' hex hex) | ('u' hex hex hex hex)

let double_quoted_string_char = 
  [^ '\r' '\n' '"' '\\'] | ('\\' escape_sequence)


rule token = parse
   | blank + { token lexbuf }
   | '\n' { new_line lexbuf; token lexbuf }
   | '\r' { new_line lexbuf; token lexbuf }
   | "\r\n" { new_line lexbuf; token lexbuf }
   | "/*" { block_comment lexbuf }
   | "//"[^ '\r' '\n']* [ '\r' '\n' ] { new_line lexbuf; token lexbuf }

   | "/*:" { parse_re := false; comment_start_p := lexeme_start_p lexbuf;
             hint lexbuf }

   (* ContinueId and BreakId are tokens for labelled break and continue.  They
    * include their target label.
    *)
   | "continue" [ ' ' '\t' ]+ (ident as x) { parse_re := false; ContinueId x }
   | "break" [ ' ' '\t' ]+ (ident as x) { parse_re := false; BreakId x }

   | '/' {if !parse_re then (parse_re := false; regexp lexbuf) else Div }

   | '"' { parse_re := false; string_lit '"' lexbuf }
   | '\'' { parse_re := false; string_lit '\'' lexbuf }
   
   | num_lit as x {  parse_re := false; parse_num_lit x }
   | "{" { parse_re := false; LBrace }
   | "}" { parse_re := false; RBrace }
   | '(' { parse_re := true; LParen }
   | ')' {  parse_re := false; RParen }
   | "|=" { parse_re := false; AssignOp OpAssignBOr }
   | "^=" { parse_re := false; AssignOp OpAssignBXor }
   | "&=" { parse_re := false; AssignOp OpAssignBAnd }
   | "<<=" { parse_re := false; AssignOp OpAssignLShift }
   | ">>=" { parse_re := false; AssignOp OpAssignZfRShift }
   | ">>>=" { parse_re := false; AssignOp OpAssignSpRShift }
   | "+=" { parse_re := false; AssignOp OpAssignAdd }
   | "-=" { parse_re := false; AssignOp OpAssignSub }
   | "*=" { parse_re := false; AssignOp OpAssignMul }
   | "/=" { parse_re := false; AssignOp OpAssignDiv }
   | "%=" { parse_re := false; AssignOp OpAssignMod }
   | "%" { parse_re := false; Mod }
   | "=" { parse_re := true; Assign }
   | ";" { parse_re := false; Semi }
   | "," { parse_re := true; Comma }
   | "?" { parse_re := true; Ques }
   | ":" { parse_re := true; Colon }
   | "||" { parse_re := true; LOr }
   | "&&" { parse_re := false; LAnd }
   | "|" { parse_re := false; BOr }
   | "^" { parse_re := false; BXor }
   | "&" { parse_re := false; BAnd }
   | "===" { parse_re := false; StrictEq }
   | "==" { parse_re := false; AbstractEq }
   | "!=" { parse_re := false; AbstractNEq }
   | "!==" { parse_re := false; StrictNEq }
   | "<<" { parse_re := false; LShift }
   | ">>" { parse_re := false; RShift }
   | ">>>" { parse_re := false; SpRShift }
   | "<=" { parse_re := false; LEq }
   | "<" { parse_re := false; LT }
   | ">=" { parse_re := false; GEq }
   | ">" { parse_re := false; GT }
   | "++" { parse_re := false; PlusPlus }
   | "--" { parse_re := false; MinusMinus }
   | "+" { parse_re := false; Plus }
   | "-" { parse_re := false; Minus }
   | "*" { parse_re := false; Times }
   | "!" { parse_re := true; Exclamation }
   | "~" { parse_re := false; Tilde }
   | "." { parse_re := false; Period }
   | "[" { parse_re := false; LBrack }
   | "]" { parse_re := false; RBrack }

   | "if" { parse_re := false; If  }
   | "else" { parse_re := false; Else  }
   | "true" { parse_re := false; True  }
   | "false" { parse_re := false; False  }
   | "new" { parse_re := false; New  }
   | "instanceof" { parse_re := false; Instanceof  }
   | "this" { parse_re := false; This  }
   | "null" { parse_re := false; Null  }
   | "function" { parse_re := false; Function  }
   | "typeof" { parse_re := false; Typeof  }
   | "void" { parse_re := false; Void  }
   | "delete" { parse_re := false; Delete  }
   | "switch" { parse_re := false; Switch  }
   | "default" { parse_re := false; Default  }
   | "case" { parse_re := false; Case  }
   | "while" { parse_re := false; While  }
   | "do" { parse_re := false; Do  }
   | "break" { parse_re := false; Break  }
   | "var" { parse_re := false; Var  }
   | "in" { parse_re := false; In  }
   | "for" { parse_re := false; For  }
   | "try" { parse_re := false; Try  }
   | "catch" { parse_re := false; Catch  }
   | "finally" { parse_re := false; Finally  }
   | "throw" { parse_re := false; Throw  }
   | "return" { parse_re := false; Return  }
   | "with" { parse_re := false; With  }
   | "continue" { parse_re := false; Continue  }
   | "instanceof" { parse_re := false; Instanceof  }
   | ident as x { parse_re := false; Id x }
   | eof { EOF }

and block_comment = parse
  | "*/" { token lexbuf }
  | '*' { block_comment lexbuf }
  | "\r\n" { new_line lexbuf; block_comment lexbuf; }
  | [ '\n' '\r' ]  { new_line lexbuf; block_comment lexbuf }
  | [^ '\n' '\r' '*'] { block_comment lexbuf }

and hint = parse
  | "*/" { let str = Buffer.contents block_comment_buf in
             Buffer.clear block_comment_buf; HINT str }
  | '*' { Buffer.add_char block_comment_buf '*'; hint lexbuf }
  | "\r\n" { new_line lexbuf; Buffer.add_char block_comment_buf '\n'; 
             hint lexbuf }
  | [ '\n' '\r' ] { new_line lexbuf; Buffer.add_char block_comment_buf '\n';
                    hint lexbuf }
  | ([^ '\n' '\r' '*'])+ as txt { Buffer.add_string block_comment_buf txt;
                                  hint lexbuf }

and string_lit end_ch = parse
  (* multi-line *)
  | "\\\r" { string_lit end_ch lexbuf }
  | "\\\n" { string_lit end_ch lexbuf }
  (* escape codes *)
  | "\\'"  { Buffer.add_char string_buf '\''; string_lit end_ch lexbuf }
  | "\\\"" { Buffer.add_char string_buf '\"'; string_lit end_ch lexbuf }
  | "\\\\" { Buffer.add_char string_buf '\\'; string_lit end_ch lexbuf }
  | "\\b" { Buffer.add_char string_buf '\b'; string_lit end_ch lexbuf }
  | "\\n" { Buffer.add_char string_buf '\n'; string_lit end_ch lexbuf }
  | "\\r" { Buffer.add_char string_buf '\r'; string_lit end_ch lexbuf }
  | "\\t" { Buffer.add_char string_buf '\t'; string_lit end_ch lexbuf }
  (* NOTE: OCaml does not support Unicode characters. See the OCaml "Batteries"
     for a library that does. *)
  | "\\v" { Buffer.add_char string_buf '\x0B'; string_lit end_ch lexbuf }
  | "\\ " { Buffer.add_char string_buf ' '; string_lit end_ch lexbuf }
  | "\\0" { Buffer.add_char string_buf '\x00'; string_lit end_ch lexbuf }
  | "\\x" (hex hex as ascii)
      { Buffer.add_char string_buf (char_of_int (int_of_string ("0x" ^ ascii)));
        string_lit end_ch lexbuf }
  (* NOTE: This is probably wrong, due to lack of Unicode support. *)
  | "\\u" (hex hex hex hex as uni)
      { Buffer.add_char string_buf (char_of_int (int_of_string ("0x" ^ uni)));
        string_lit end_ch lexbuf }
  | _ as ch
      { if end_ch = ch then
          String (get_string ())
        else
          (Buffer.add_char string_buf ch; 
           string_lit end_ch lexbuf)
      }

and regexp = parse
  | "/" { Regexp (get_string (), false, false) }
  | "/mg" { Regexp (get_string (), true, false) } (* TODO: m-flag ignored *)
  | "/gi" { Regexp (get_string (), true, true) }
  | "/g" { Regexp (get_string (), true, false) }
  | "/i" { Regexp (get_string (), false, true) }
  | '\\' (_ as ch) { Buffer.add_char string_buf ch; regexp lexbuf }
  | _ as ch { Buffer.add_char string_buf ch; regexp lexbuf }
