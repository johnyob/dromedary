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
                   └──Constructor alphas: a b
                   └──Constructor type:
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Variable: b
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: a11292
                         └──Type expr: Arrow
                            └──Type expr: Variable: a11295
                            └──Type expr: Variable: a11295
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: a11292
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Variable: a11292
                            └──Type expr: Variable: a11295
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: a11292,a11295
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: a11292
                            └──Type expr: Arrow
                               └──Type expr: Variable: a11295
                               └──Type expr: Variable: a11295
                         └──Type expr: Arrow
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: a11292
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: int
                                  └──Type expr: Constructor: int
                            └──Type expr: Arrow
                               └──Type expr: Variable: a11292
                               └──Type expr: Variable: a11295
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: a11292
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a11295
                                  └──Type expr: Variable: a11295
                            └──Desc: Variable: eq1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: a11292
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a11292
                                  └──Type expr: Variable: a11295
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: a11292
                                     └──Type expr: Arrow
                                        └──Type expr: Constructor: int
                                        └──Type expr: Constructor: int
                                  └──Desc: Variable: eq2
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a11292
                                     └──Type expr: Variable: a11295
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: a11292
                                        └──Desc: Variable: g
                                     └──Expression:
                                        └──Type expr: Variable: a11295
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a11292
                                                 └──Type expr: Arrow
                                                    └──Type expr: Variable: a11295
                                                    └──Type expr: Variable: a11295
                                              └──Desc: Variable
                                                 └──Variable: eq1
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: a11292
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: a11295
                                                 └──Type expr: Variable: a11295
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a11292
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: a11295
                                                          └──Type expr: Variable: a11295
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Refl
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a11292
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: a11295
                                                                   └──Type expr: Variable: a11295
                                                 └──Expression:
                                                    └──Type expr: Variable: a11295
                                                    └──Desc: Match
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a11292
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: eq2
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a11292
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: int
                                                       └──Cases:
                                                          └──Case:
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: a11292
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: int
                                                                      └──Type expr: Constructor: int
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: a11292
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: int
                                                                               └──Type expr: Constructor: int
                                                             └──Expression:
                                                                └──Type expr: Variable: a11295
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Variable: a11292
                                                                      └──Desc: Variable
                                                                         └──Variable: g
                                                                   └──Expression:
                                                                      └──Type expr: Variable: a11295
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
                   └──Constructor alphas: a b
                   └──Constructor type:
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Variable: b
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: a11373
                         └──Type expr: Arrow
                            └──Type expr: Variable: a11376
                            └──Type expr: Variable: a11376
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: a11373
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Variable: a11373
                            └──Type expr: Constructor: int
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: a11373,a11376
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: a11373
                            └──Type expr: Arrow
                               └──Type expr: Variable: a11376
                               └──Type expr: Variable: a11376
                         └──Type expr: Arrow
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: a11373
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: int
                                  └──Type expr: Constructor: int
                            └──Type expr: Arrow
                               └──Type expr: Variable: a11373
                               └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: a11373
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a11376
                                  └──Type expr: Variable: a11376
                            └──Desc: Variable: eq1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: a11373
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a11373
                                  └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: a11373
                                     └──Type expr: Arrow
                                        └──Type expr: Constructor: int
                                        └──Type expr: Constructor: int
                                  └──Desc: Variable: eq2
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a11373
                                     └──Type expr: Constructor: int
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: a11373
                                        └──Desc: Variable: g
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a11373
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: eq2
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: a11373
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a11373
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: int
                                                          └──Type expr: Constructor: int
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Refl
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a11373
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: int
                                                                   └──Type expr: Constructor: int
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Match
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a11373
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a11376
                                                                └──Type expr: Variable: a11376
                                                          └──Desc: Variable
                                                             └──Variable: eq1
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a11373
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a11376
                                                             └──Type expr: Variable: a11376
                                                       └──Cases:
                                                          └──Case:
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: a11373
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a11376
                                                                      └──Type expr: Variable: a11376
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: a11373
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Variable: a11376
                                                                               └──Type expr: Variable: a11376
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Variable: a11373
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
                   └──Constructor alphas: a b
                   └──Constructor type:
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Variable: b
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: a11452
                         └──Type expr: Arrow
                            └──Type expr: Variable: a11455
                            └──Type expr: Variable: a11455
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: a11452
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Variable: a11452
                            └──Type expr: Variable: a11455
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: a11452,a11455
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: a11452
                            └──Type expr: Arrow
                               └──Type expr: Variable: a11455
                               └──Type expr: Variable: a11455
                         └──Type expr: Arrow
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: a11452
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: int
                                  └──Type expr: Constructor: int
                            └──Type expr: Arrow
                               └──Type expr: Variable: a11452
                               └──Type expr: Variable: a11455
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: a11452
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a11455
                                  └──Type expr: Variable: a11455
                            └──Desc: Variable: eq1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: a11452
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a11452
                                  └──Type expr: Variable: a11455
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: a11452
                                     └──Type expr: Arrow
                                        └──Type expr: Constructor: int
                                        └──Type expr: Constructor: int
                                  └──Desc: Variable: eq2
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a11452
                                     └──Type expr: Variable: a11455
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: a11452
                                        └──Desc: Variable: g
                                     └──Expression:
                                        └──Type expr: Variable: a11455
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a11452
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: eq2
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: a11452
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a11452
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: int
                                                          └──Type expr: Constructor: int
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Refl
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a11452
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: int
                                                                   └──Type expr: Constructor: int
                                                 └──Expression:
                                                    └──Type expr: Variable: a11455
                                                    └──Desc: Match
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a11452
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a11455
                                                                └──Type expr: Variable: a11455
                                                          └──Desc: Variable
                                                             └──Variable: eq1
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a11452
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a11455
                                                             └──Type expr: Variable: a11455
                                                       └──Cases:
                                                          └──Case:
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: a11452
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a11455
                                                                      └──Type expr: Variable: a11455
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: a11452
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Variable: a11455
                                                                               └──Type expr: Variable: a11455
                                                             └──Expression:
                                                                └──Type expr: Variable: a11455
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Variable: a11452
                                                                      └──Desc: Variable
                                                                         └──Variable: g
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Constant: 3 |}]
