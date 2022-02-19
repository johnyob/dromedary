(*****************************************************************************)
(*                                                                           *)
(*                                Dromedary                                  *)
(*                                                                           *)
(*                Alistair O'Brien, University of Cambridge                  *)
(*                                                                           *)
(* Copyright 2021 Alistair O'Brien.                                          *)
(*                                                                           *)
(* All rights reserved. This file is distributed under the terms of the MIT  *)
(* license, as described in the file LICENSE.                                *)
(*                                                                           *)
(*****************************************************************************)

{
open Parser

module Lexer_util = MenhirLib.LexerUtil 
exception Lexer_error of string
}

let upper = ['A' - 'Z']
let lower = ['a' - 'z']
let letter = lower | upper
 
let digit = ['0' - '9']
let space = [' ' '\t']
let newline = '\r'? '\n'

let id_char = lower | digit | ['_' '\'']
let id = lower id_char*
let con_id = upper id_char*

let sign = '-'?
let int = sign digit+

let frac = '.' digit+
let float = sign (int? frac | int '.')

rule read = 
  parse
  (* keywords *)
  | "let"                         { LET }
  | "rec"                         { REC }
  | "and"                         { AND }
  | "in"                          { IN }
  | "if"                          { IF }
  | "then"                        { THEN }
  | "else"                        { ELSE }
  | "true"                        { TRUE }
  | "false"                       { FALSE }
  | "fun"                         { FUN }
  | "while"                       { WHILE }
  | "do"                          { DO }
  | "done"                        { DONE }
  | "for"                         { FOR }
  | "to"                          { TO }
  | "downto"                      { DOWNTO }
  | "try"                         { TRY }
  | "match"                       { MATCH }
  | "with"                        { WITH }
  | "forall"                      { FORALL }
  | "exists"                      { EXISTS }
  | "type"                        { TYPE }
  | "as"                          { AS }
  | "ref"                         { REF }

  (* reserved operators *)
  | "->"                          { RIGHT_ARROW }
  | ":"                           { COLON }
  | "="                           { EQUAL }
  | "."                           { DOT }
  | ","                           { COMMA }
  | ";"                           { SEMI_COLON }
  | "*"                           { STAR }
  | "_"                           { UNDERSCORE }
  | "\'"                          { QUOTE }
  | "|"                           { BAR }


  (* comments *)
  | "(*"                          { read_comment lexbuf }

  (* primitive operators (fixed in Dromedary) *)
  | ":="                          { OP_ASSIGN }
  | "!"                           { OP_DEREF }

  (* | "<>"                          { OP_NOT_EQUAL }
  | "<="                          { OP_LESS_EQUAL }
  | "<"                           { OP_LESS }
  | ">="                          { OP_GREATER_EQUAL }
  | ">"                           { OP_GREATER } *)
(*   
  | "||"                          { OP_OR }
  | "&&"                          { OP_AND } *)
(* 
  | "*."                          { OP_FTIMES }
  | "+."                          { OP_FPLUS }
  | "-."                          { OP_FMINUS }
  | "/."                          { OP_FDIVIDE }
  | "**"                          { OP_FEXP } *)

  | "+"                           { OP_PLUS }
  | "-"                           { OP_MINUS }
  | "/"                           { OP_DIVIDE }

  (* identifiers *)
  | id                            { IDENT (Lexing.lexeme lexbuf) }
  | con_id                        { CON_IDENT (Lexing.lexeme lexbuf) }

  (* unit literal *)
  | "()"                          { UNIT }

  (* number literals *)
  | int                           { INT (int_of_string (Lexing.lexeme lexbuf)) }
  (* | float                         { FLOAT (float_of_string (Lexing.lexeme lexbuf)) } *)

  | space+                        { read lexbuf }
  | newline                       { Lexer_util.newline lexbuf; read lexbuf }


  (* braces *)
  | "("                           { LEFT_PAREN }
  | ")"                           { RIGHT_PAREN }
  | "{"                           { LEFT_BRACE }
  | "}"                           { RIGHT_BRACE }

  | eof                           { EOF }
  | _                             { raise (Lexer_error ("Unexpected character: " ^ Lexing.lexeme lexbuf)) }

(** Read a comment delimited by (* ... *)
    Nesting is not permitted. *)
and read_comment = 
  parse
  | "*)"                          { read lexbuf }
  | eof                           { raise (Lexer_error "Unclosed comment") }
  | _                             { read_comment lexbuf }
