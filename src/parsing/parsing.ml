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