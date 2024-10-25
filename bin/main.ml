module Parsing_ = Parsing
open Core
open Parsing_
open Typing

let parse_structure_from_string ~f str =
  match parse_structure_from_string str with
  | Ok pstr -> f pstr
  | Error err ->
    (match err with
     | `Lexer_error message -> [%sexp ("lexer error: " ^ message : string)]
     | `Parser_error -> [%sexp ("parse error" : string)])
    |> Sexp.to_string_hum
    |> print_endline


let print_infer_result ?(debug = false) str =
  parse_structure_from_string str ~f:(fun pstr ->
    let tstr = Typing.infer_str ~debug pstr in
    match tstr with
    | Ok tstr -> Typedtree.pp_structure_mach Format.std_formatter tstr
    | Error err -> Sexp.to_string_hum err |> print_endline)


let () =
  let str =
    {|
      external failwith : 'a. string -> 'a = "%failwith";;    
    |}
  in
  print_infer_result ~debug:true str
