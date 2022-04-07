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
                      └──Constructor betas: a b
                      └──Type expr: Tuple
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                         └──Type expr: Arrow
                            └──Type expr: Variable: a
                            └──Type expr: Constructor: unit |}]