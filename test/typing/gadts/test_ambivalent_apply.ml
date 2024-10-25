open! Import
open Util

(* Tests from typing-gadts/ambivalent-apply.ml
   -------------------------------------------
   Test count: 4/4

   Passes 2 test that should fail.

   The PR mentions a "bug" in the original
   ambivalentspaper which the author was not
   aware of. Thus considered out of scope.
*)

let%expect_test "ambivalent-apply-1" =
  let str =
    {|
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      let (type 'a 'b) f = 
        fun (eq1 : ('a, 'b -> 'b) eq) (eq2 : ('a, int -> int) eq) (g : 'a) ->
          match eq1 with
          (Refl ->
              match eq2 with
              ( Refl -> g 3 ))
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: eq
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Refl
                   └──Constructor alphas: 161 162
                   └──Constructor type:
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: 161
                         └──Type expr: Variable: 162
                   └──Constraint:
                      └──Type expr: Variable: 161
                      └──Type expr: Variable: 162
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: 14
                         └──Type expr: Arrow
                            └──Type expr: Variable: 17
                            └──Type expr: Variable: 17
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: 14
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Variable: 14
                            └──Type expr: Variable: 17
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: 14,17
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: 14
                            └──Type expr: Arrow
                               └──Type expr: Variable: 17
                               └──Type expr: Variable: 17
                         └──Type expr: Arrow
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: 14
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: int
                                  └──Type expr: Constructor: int
                            └──Type expr: Arrow
                               └──Type expr: Variable: 14
                               └──Type expr: Variable: 17
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: 14
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 17
                                  └──Type expr: Variable: 17
                            └──Desc: Variable: eq1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: 14
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 14
                                  └──Type expr: Variable: 17
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: 14
                                     └──Type expr: Arrow
                                        └──Type expr: Constructor: int
                                        └──Type expr: Constructor: int
                                  └──Desc: Variable: eq2
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 14
                                     └──Type expr: Variable: 17
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: 14
                                        └──Desc: Variable: g
                                     └──Expression:
                                        └──Type expr: Variable: 17
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: 14
                                                 └──Type expr: Arrow
                                                    └──Type expr: Variable: 17
                                                    └──Type expr: Variable: 17
                                              └──Desc: Variable
                                                 └──Variable: eq1
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: 14
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: 17
                                                 └──Type expr: Variable: 17
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: 14
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: 17
                                                          └──Type expr: Variable: 17
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Refl
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: 14
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: 17
                                                                   └──Type expr: Variable: 17
                                                 └──Expression:
                                                    └──Type expr: Variable: 17
                                                    └──Desc: Match
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: 14
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: eq2
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: 14
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: int
                                                       └──Cases:
                                                          └──Case:
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: 14
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: int
                                                                      └──Type expr: Constructor: int
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: 14
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: int
                                                                               └──Type expr: Constructor: int
                                                             └──Expression:
                                                                └──Type expr: Variable: 17
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Variable: 14
                                                                      └──Desc: Variable
                                                                         └──Variable: g
                                                                   └──Expression:
                                                                      └──Type expr: Variable: 17
                                                                      └──Desc: Constant: 3 |}]


let%expect_test "ambivalent-apply-2" =
  let str =
    {|
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      let (type 'a 'b) f = 
        fun (eq1 : ('a, 'b -> 'b) eq) (eq2 : ('a, int -> int) eq) (g : 'a) ->
          match eq2 with
          (Refl ->
              match eq1 with
              ( Refl -> g 3 ))
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: eq
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Refl
                   └──Constructor alphas: 81 82
                   └──Constructor type:
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: 81
                         └──Type expr: Variable: 82
                   └──Constraint:
                      └──Type expr: Variable: 81
                      └──Type expr: Variable: 82
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: 14
                         └──Type expr: Arrow
                            └──Type expr: Variable: 17
                            └──Type expr: Variable: 17
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: 14
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Variable: 14
                            └──Type expr: Constructor: int
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: 14,17
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: 14
                            └──Type expr: Arrow
                               └──Type expr: Variable: 17
                               └──Type expr: Variable: 17
                         └──Type expr: Arrow
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: 14
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: int
                                  └──Type expr: Constructor: int
                            └──Type expr: Arrow
                               └──Type expr: Variable: 14
                               └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: 14
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 17
                                  └──Type expr: Variable: 17
                            └──Desc: Variable: eq1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: 14
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 14
                                  └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: 14
                                     └──Type expr: Arrow
                                        └──Type expr: Constructor: int
                                        └──Type expr: Constructor: int
                                  └──Desc: Variable: eq2
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 14
                                     └──Type expr: Constructor: int
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: 14
                                        └──Desc: Variable: g
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: 14
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: eq2
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: 14
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: 14
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: int
                                                          └──Type expr: Constructor: int
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Refl
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: 14
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: int
                                                                   └──Type expr: Constructor: int
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Match
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: 14
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: 17
                                                                └──Type expr: Variable: 17
                                                          └──Desc: Variable
                                                             └──Variable: eq1
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: 14
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 17
                                                             └──Type expr: Variable: 17
                                                       └──Cases:
                                                          └──Case:
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: 14
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: 17
                                                                      └──Type expr: Variable: 17
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: 14
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Variable: 17
                                                                               └──Type expr: Variable: 17
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Variable: 14
                                                                      └──Desc: Variable
                                                                         └──Variable: g
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Constant: 3 |}]


let%expect_test "ambivalent-apply-3" =
  let str =
    {|
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      let (type 'a 'b) f = 
        fun (eq1 : ('a, 'b -> 'b) eq) (eq2 : ('a, int -> int) eq) (g : 'a) ->
          (match eq2 with
          (Refl ->
              match eq1 with
              ( Refl -> g 3 )) : 'b)
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: eq
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Refl
                   └──Constructor alphas: 79 80
                   └──Constructor type:
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: 79
                         └──Type expr: Variable: 80
                   └──Constraint:
                      └──Type expr: Variable: 79
                      └──Type expr: Variable: 80
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: 14
                         └──Type expr: Arrow
                            └──Type expr: Variable: 17
                            └──Type expr: Variable: 17
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: 14
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Variable: 14
                            └──Type expr: Variable: 17
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: 14,17
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: 14
                            └──Type expr: Arrow
                               └──Type expr: Variable: 17
                               └──Type expr: Variable: 17
                         └──Type expr: Arrow
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: 14
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: int
                                  └──Type expr: Constructor: int
                            └──Type expr: Arrow
                               └──Type expr: Variable: 14
                               └──Type expr: Variable: 17
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: 14
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 17
                                  └──Type expr: Variable: 17
                            └──Desc: Variable: eq1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: 14
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 14
                                  └──Type expr: Variable: 17
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: 14
                                     └──Type expr: Arrow
                                        └──Type expr: Constructor: int
                                        └──Type expr: Constructor: int
                                  └──Desc: Variable: eq2
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 14
                                     └──Type expr: Variable: 17
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: 14
                                        └──Desc: Variable: g
                                     └──Expression:
                                        └──Type expr: Variable: 17
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: 14
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: eq2
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: 14
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: 14
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: int
                                                          └──Type expr: Constructor: int
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Refl
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: 14
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: int
                                                                   └──Type expr: Constructor: int
                                                 └──Expression:
                                                    └──Type expr: Variable: 17
                                                    └──Desc: Match
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: 14
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: 17
                                                                └──Type expr: Variable: 17
                                                          └──Desc: Variable
                                                             └──Variable: eq1
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: 14
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 17
                                                             └──Type expr: Variable: 17
                                                       └──Cases:
                                                          └──Case:
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: 14
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: 17
                                                                      └──Type expr: Variable: 17
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: 14
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Variable: 17
                                                                               └──Type expr: Variable: 17
                                                             └──Expression:
                                                                └──Type expr: Variable: 17
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Variable: 14
                                                                      └──Desc: Variable
                                                                         └──Variable: g
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Constant: 3 |}]
