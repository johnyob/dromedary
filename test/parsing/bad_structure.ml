open! Import
open Util

let%expect_test "no trailing ;;" =
  let str = 
    {|
      let valid_function = fun () -> 1
    |}
  in
  print_structure_parsetree str;
  [%expect {| "parse error" |}]

let%expect_test "type definition - empty case" =
  let str = 
    {|
      type t = 
        |
        | A of int
        | B of bool 
      ;;
    |}
  in
  print_structure_parsetree str;
  [%expect {| "parse error" |}]


let%expect_test "exception - existentials" =
  let str = 
    {|
      exception Existential of 'a. 'a;;
    |}
  in
  print_structure_parsetree str;
  [%expect {| "parse error" |}]


let%expect_test "type definition - empty variant" =
  let str = 
    {|
      type t = |;;
    |}
  in
  print_structure_parsetree str;
  [%expect {| "parse error" |}]

let%expect_test "type definition - empty record" =
  let str = 
    {|
      type t = {};;
    |}
  in
  print_structure_parsetree str;
  [%expect {| "parse error" |}]


