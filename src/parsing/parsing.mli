open Core

module Ast_types = Ast_types
module Parsetree = Parsetree

type error = 
  [ `Lexer_error of string
  | `Parser_error
  ]

val parse_string : string -> (Parsetree.expression, error) Result.t 