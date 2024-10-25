open! Import

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


let print_constraint_result str =
  parse_structure_from_string str ~f:(fun pstr ->
    let open Typing.Private in
    let cstr = Infer_structure.infer_str ~env:Env.empty pstr in
    (match cstr with
     | Ok (_, cstr) -> Constraint.Structure.sexp_of_t cstr
     | Error err -> err)
    |> Sexp.to_string_hum
    |> print_endline)
