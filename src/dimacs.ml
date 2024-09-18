
let parse_lexbuf : string -> Lexing.lexbuf -> Ast.t = fun fname lexbuf ->
  LexerDimacs.filename := fname;
  try
   ParserDimacs.file LexerDimacs.token lexbuf
  with
  | ParserDimacs.Error ->
    let loc = Lexing.(lexbuf.lex_start_p) in
    let loc = Some(LexerDimacs.locate loc loc) in
    Console.fatal loc "Unexpected token [%s]." (Lexing.lexeme lexbuf)

let parse_file : string -> Ast.t = fun fname ->
  let ic = open_in fname in
  let lexbuf = Lexing.from_channel ic in
  try let l = parse_lexbuf fname lexbuf in close_in ic; l
  with e -> close_in ic; raise e
