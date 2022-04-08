open! Import
open Util

(* Tests from typing-gadts/nested_equations.ml
   -------------------------------------------
   Test count: 2/8

   2 tests are removed due to reliance on 
   abstract types as "equatable" variables.
   This is an implementation detail of GADTs
   in OCaml.

   4 tests are removed due to reliance on 
   modules
*)

let%expect_test "nested-equations-1" =
  let str = 
    {|
      type 'a t = 
        | Int constraint 'a = int
      ;;

      let (type 'a) to_int = 
        fun (w : 'a t) (x : 'a) ->
          (match w with (Int -> x) : int)
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
                   └──Constructor name: Int
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: int
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a8861
                      └──Type expr: Arrow
                         └──Type expr: Variable: a8861
                         └──Type expr: Constructor: int
                   └──Desc: Variable: to_int
                └──Abstraction:
                   └──Variables: a8861
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a8861
                         └──Type expr: Arrow
                            └──Type expr: Variable: a8861
                            └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: a8861
                            └──Desc: Variable: w
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a8861
                               └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: a8861
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: a8861
                                        └──Desc: Variable
                                           └──Variable: w
                                     └──Type expr: Constructor: t
                                        └──Type expr: Variable: a8861
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: a8861
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Int
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a8861
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: x |}]

let%expect_test "nested-equations-2" =
  let str = 
    {|
      type 'a t = 
        | Int constraint 'a = int
      ;;

      external magic : 'a 'b. 'a -> 'b = "%magic";;

      let w_bool = (magic 0 : bool t);;
      let f_bool = 
        fun (x : bool) ->
          (match w_bool with (Int -> x) : int)
      ;;
    |}
  in
  print_infer_result str;
  [%expect{| "Inconsistent equations added by local branches" |}]


