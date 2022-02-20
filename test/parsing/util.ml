open! Import

let print_parsetree exp = 
  match parse_string exp with
  | Ok parsetree -> Parsetree.pp_expression_mach Format.std_formatter parsetree
  | Error err ->
    (match err with
    | `Lexer_error message -> [%sexp ("lexer error" ^ message : string)]
    | `Parser_error -> [%sexp ("parse error" : string)])
    |> Sexp.to_string_hum
    |> print_endline