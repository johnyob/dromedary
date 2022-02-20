open Core

module Ast_types = Ast_types
module Parsetree = Parsetree

type error = 
  [ `Lexer_error of string
  | `Parser_error
  ]

let parse lexbuf =
  try Parser.parse Lexer.read lexbuf |> Result.Ok with
  | Lexer.Lexer_error message -> 
    Result.Error (`Lexer_error message)
  | Parser.Error ->
    Result.Error `Parser_error

let parse_string str = 
  parse (Lexing.from_string str)