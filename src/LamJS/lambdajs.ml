open Prelude
open Lambdajs_syntax
open Lexing

let parse_lambdajs cin name =
  let lexbuf = Lexing.from_channel cin in
    try 
      (* Set the correct filename in lexbuf (for source-tracking). *)
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = name };
      Lambdajs_parser.prog Lambdajs_lexer.token lexbuf
    with
      |  Failure "lexing: empty token" ->
           failwith (sprintf "lexical error at %s"
                       (string_of_position 
                          (lexbuf.lex_curr_p, lexbuf.lex_curr_p)))
      | Lambdajs_parser.Error ->
           failwith (sprintf "parse error at %s; unexpected token %s"
                       (string_of_position 
                          (lexbuf.lex_curr_p, lexbuf.lex_curr_p))
                       (lexeme lexbuf))
