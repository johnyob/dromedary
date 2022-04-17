open! Import
open Util

let%expect_test "" = 
  let str = 
    {|
      type t = 
        | A of 'a 'b. 'a * 'b * ('a -> unit) 
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: t
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: A
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: t
                   └──Constructor argument:
                      └──Constructor betas: 15511 15510
                      └──Type expr: Tuple
                         └──Type expr: Variable: 15510
                         └──Type expr: Variable: 15511
                         └──Type expr: Arrow
                            └──Type expr: Variable: 15510
                            └──Type expr: Constructor: unit |}]