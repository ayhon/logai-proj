{
  open TokensDimacs

  let filename = ref ""

  let locate : Lexing.position -> Lexing.position -> Location.pos = fun p1 p2 ->
    let open Location in
    let fname = if !filename = "" then None else Some(!filename) in
    let start_line = p1.pos_lnum in
    let start_col = p1.pos_cnum - p1.pos_bol in
    let end_line = p2.pos_lnum in
    let end_col = p2.pos_cnum - p2.pos_bol in
    Lazy.from_val {fname; start_line; start_col; end_line; end_col}

  let locate_lexbuf : Lexing.lexbuf -> Location.pos = fun lexbuf ->
      locate lexbuf.lex_start_p lexbuf.lex_curr_p

  let unexpected_char : Lexing.lexbuf -> char -> token = fun lexbuf c ->
      Console.fatal (Some(locate_lexbuf lexbuf)) "Unexpected characters [%c]." c
}

let zero_numeric = '0'
let numeric = ['0' - '9']
let non_zero_numeric = ['1' - '9']

let positive_number = non_zero_numeric numeric*
let negative_number = ['-'] positive_number
let number = positive_number | negative_number

let printable_char = [^ '\n']
let comment = ['c'] printable_char* ['\n']

rule token = parse
  | "c"             { comment lexbuf }
  | "p"             { P }
  | "cnf"           { CNF }
  | eof             { EOF }
  | zero_numeric    { ZERO }
  | [' ' '\t' '\r'] { token lexbuf }
  | number          { INT (int_of_string @@ Lexing.lexeme lexbuf) }
  | '\n'            { Lexing.new_line lexbuf; NEWLINE }
  | _ as c          { unexpected_char lexbuf c }

and comment = parse
  | '\n'  { Lexing.new_line lexbuf; token lexbuf }
  | printable_char { comment lexbuf }