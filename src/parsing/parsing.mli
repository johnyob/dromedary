open Core

module Ast_types = Ast_types
module Parsetree = Parsetree

type error = 
  [ `Lexer_error of string
  | `Parser_error
  ]

val parse_expression_from_string : string -> (Parsetree.expression, error) Result.t 

val parse_structure_from_string : string -> (Parsetree.structure, error) Result.t

val tokens_from_string : string -> (Parser.token list, [ `Lexer_error of string ]) Result.t

val pp_token : Parser.token Fmt.t
