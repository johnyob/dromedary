open! Import
open Util

let%expect_test "variable : doesn't begin w/ lower alpha" =
  let exp = {| _x |} in
  print_expression_parsetree exp;
  [%expect {| "parse error" |}]

let%expect_test "core_type : unclosed tuple" =
  let exp = {| (x : int * ) |} in
  print_expression_parsetree exp;
  [%expect {| "parse error" |}]

let%expect_test "core_type : trailing argument comma" =
  let exp = {| (x : ('a, ) list) |} in
  print_expression_parsetree exp;
  [%expect {| "parse error" |}]

let%expect_test "core_type : trailing arrow" =
  let exp = {| (x : int -> ) |} in
  print_expression_parsetree exp;
  [%expect {| "parse error" |}]

let%expect_test "let : no function syntax" =
  let exp = {| let fst (x, y) = x in () |} in
  print_expression_parsetree exp;
  [%expect {| "parse error" |}]

let%expect_test "let : trailing in" =
  let exp = {| let x = 1 |} in
  print_expression_parsetree exp;
  [%expect {| "parse error" |}]

let%expect_test "if : trailing else" =
  let exp = {| if true then 3 |} in
  print_expression_parsetree exp;
  [%expect {| "parse error" |}]

let%expect_test "pattern : swap expr and pat" =
  let exp = {| fun (fun () -> a) -> _ |} in
  print_expression_parsetree exp;
  [%expect {| "parse error" |}]

let%expect_test "pattern : non-atomic pattern" =
  let exp = {| fun Cons x as t -> 1 |} in
  print_expression_parsetree exp;
  [%expect {| "parse error" |}]

let%expect_test "unclosed brackets" =
  let exp = {| ((1 + 1) + 2 |} in
  print_expression_parsetree exp;
  [%expect {| "parse error" |}]

let%expect_test "unterminated string" =
  let exp = {| "Hello, is it me you're looking for |} in
  print_expression_parsetree exp;
  [%expect {| "lexer error: String is not terminated" |}]

let%expect_test "unterminated comment" =
  let exp =
    {|
      (* This function does some cool stuff
      let foo () = bar in ()
    |}
  in
  print_expression_parsetree exp;
  [%expect {| "lexer error: Unclosed comment" |}]