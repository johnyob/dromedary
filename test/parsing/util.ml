open! Import

let print_expression_parsetree exp =
  match parse_expression_from_string exp with
  | Ok parsetree -> Parsetree.pp_expression_mach Format.std_formatter parsetree
  | Error err ->
    (match err with
     | `Lexer_error message -> [%sexp ("lexer error: " ^ message : string)]
     | `Parser_error -> [%sexp ("parse error" : string)])
    |> Sexp.to_string_hum
    |> print_endline


let print_structure_parsetree str =
  match parse_structure_from_string str with
  | Ok parsetree -> Parsetree.pp_structure_mach Format.std_formatter parsetree
  | Error err ->
    (match err with
     | `Lexer_error message -> [%sexp ("lexer error: " ^ message : string)]
     | `Parser_error -> [%sexp ("parse error" : string)])
    |> Sexp.to_string_hum
    |> print_endline


let print_tokens str =
  match tokens_from_string str with
  | Ok tokens -> List.iter ~f:(pp_token Format.std_formatter) tokens
  | Error (`Lexer_error message) ->
    [%sexp ("lexer error: " ^ message : string)]
    |> Sexp.to_string_hum
    |> print_endline
