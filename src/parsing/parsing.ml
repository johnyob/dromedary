open Core
module Ast_types = Ast_types
module Parsetree = Parsetree

type error =
  [ `Lexer_error of string
  | `Parser_error
  ]

let parse ~f lexbuf =
  try f Lexer.read lexbuf |> Result.Ok with
  | Lexer.Lexer_error message -> Result.Error (`Lexer_error message)
  | Parser.Error -> Result.Error `Parser_error


let parse_expression = parse ~f:Parser.parse_expression
let parse_structure = parse ~f:Parser.parse_structure
let parse_expression_from_string str = parse_expression (Lexing.from_string str)
let parse_structure_from_string str = parse_structure (Lexing.from_string str)

let pp_token ppf =
  let open Parser in
  function
  | LET -> Format.fprintf ppf "LET@."
  | REC -> Format.fprintf ppf "REC@."
  | AND -> Format.fprintf ppf "AND@."
  | IN -> Format.fprintf ppf "IN@."
  | IF -> Format.fprintf ppf "IF@."
  | THEN -> Format.fprintf ppf "THEN@."
  | ELSE -> Format.fprintf ppf "ELSE@."
  | FUN -> Format.fprintf ppf "FUN@."
  | WHILE -> Format.fprintf ppf "WHILE@."
  | DO -> Format.fprintf ppf "DO@."
  | DONE -> Format.fprintf ppf "DONE@."
  | FOR -> Format.fprintf ppf "FOR@."
  | TO -> Format.fprintf ppf "TO@."
  | DOWNTO -> Format.fprintf ppf "DOWNTO@."
  | TRY -> Format.fprintf ppf "TRY@."
  | WITH -> Format.fprintf ppf "WITH@."
  | MATCH -> Format.fprintf ppf "MATCH@."
  | FORALL -> Format.fprintf ppf "FORALL@."
  | EXISTS -> Format.fprintf ppf "EXISTS@."
  | TYPE -> Format.fprintf ppf "TYPE@."
  | AS -> Format.fprintf ppf "AS@."
  | OF -> Format.fprintf ppf "OF@."
  | EXCEPTION -> Format.fprintf ppf "EXCEPTION@."
  | EXTERNAL -> Format.fprintf ppf "EXTERNAL@."
  | CONSTRAINT -> Format.fprintf ppf "CONSTRAINT@."
  | SEMI_SEMI_COLON -> Format.fprintf ppf "SEMI_SEMI_COLON@."
  | RIGHT_ARROW -> Format.fprintf ppf "RIGHT_ARROW@."
  | COLON -> Format.fprintf ppf "COLON@."
  | EQUAL -> Format.fprintf ppf "EQUAL@."
  | DOT -> Format.fprintf ppf "DOT@."
  | COMMA -> Format.fprintf ppf "COMMA@."
  | SEMI_COLON -> Format.fprintf ppf "SEMI_COLON@."
  | STAR -> Format.fprintf ppf "STAR@."
  | UNDERSCORE -> Format.fprintf ppf "UNDERSCORE@."
  | QUOTE -> Format.fprintf ppf "QUOTE@."
  | BACKTICK -> Format.fprintf ppf "BACKTICK@."
  | BAR -> Format.fprintf ppf "BAR@."
  | REF -> Format.fprintf ppf "REF@."
  | OP_ASSIGN -> Format.fprintf ppf "OP_ASSIGN@."
  | OP_DEREF -> Format.fprintf ppf "OP_DEREF@."
  | OP_PLUS -> Format.fprintf ppf "OP_PLUS@."
  | OP_MINUS -> Format.fprintf ppf "OP_MINUS@."
  | OP_DIVIDE -> Format.fprintf ppf "OP_DIVIDE@."
  | TRUE -> Format.fprintf ppf "TRUE@."
  | FALSE -> Format.fprintf ppf "FALSE@."
  | CHAR c -> Format.fprintf ppf "CHAR(%c)@." c
  | STRING s -> Format.fprintf ppf "STRING(%s)@." s
  | INT i -> Format.fprintf ppf "INT(%d)@." i
  | FLOAT f -> Format.fprintf ppf "FLOAT(%f)@." f
  | UNIT -> Format.fprintf ppf "UNIT@."
  | IDENT id -> Format.fprintf ppf "IDENT(%s)@." id
  | CON_IDENT con_id -> Format.fprintf ppf "CON_IDENT(%s)@." con_id
  | LEFT_PAREN -> Format.fprintf ppf "LEFT_PAREN@."
  | RIGHT_PAREN -> Format.fprintf ppf "RIGHT_PAREN@."
  | LEFT_BRACE -> Format.fprintf ppf "LEFT_BRACE@."
  | RIGHT_BRACE -> Format.fprintf ppf "RIGHT_BRACE@."
  | LEFT_BRACKET -> Format.fprintf ppf "LEFT_BRACKET@."
  | RIGHT_BRACKET -> Format.fprintf ppf "RIGHT_BRACKET@."
  | LESS -> Format.fprintf ppf "LESS@."
  | GREATER -> Format.fprintf ppf "GREATER@."
  | MU -> Format.fprintf ppf "MU@."
  | WHERE -> Format.fprintf ppf "WHERE@."
  | EOF -> Format.fprintf ppf "EOF@."


let tokens_from_string str =
  let rec loop lexbuf =
    match Lexer.read lexbuf with
    | Parser.EOF -> []
    | token -> token :: loop lexbuf
  in
  try Ok (loop (Lexing.from_string str)) with
  | Lexer.Lexer_error err -> Error (`Lexer_error err)
