open! Import
open Util

let%expect_test "" = 
  let str = 
    {|
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      external hole : 'a. 'a = "%hole";;

      let (type 't) f = 
        fun (t1 : (int, 't) eq) (t2 : (string, 't) eq) ->
          match (t1, t2) with
          ( (Refl, Refl) -> hole )
      ;;
    |}
  in
  print_infer_result str;
  [%expect {| "Inconsistent equations added by local branches" |}]

let%expect_test "" = 
  let str = 
    {|
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      external hole : 'a. 'a = "%hole";;

      type 'a option = 
        | None
        | Some of 'a
      ;;

      let (type 't) f = 
        fun (t : ((int, 't) eq * (string, 't) eq) option) ->
          match t with ( None -> () )
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
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
       └──Structure item: Primitive
          └──Value description:
             └──Name: hole
             └──Scheme:
                └──Variables: a5764
                └──Type expr: Variable: a5764
             └──Primitive name: %hole
       └──Structure item: Type
          └──Type declaration:
             └──Type name: option
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: None
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: a
                └──Constructor declaration:
                   └──Constructor name: Some
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: a
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: option
                         └──Type expr: Tuple
                            └──Type expr: Constructor: eq
                               └──Type expr: Constructor: int
                               └──Type expr: Variable: a5795
                            └──Type expr: Constructor: eq
                               └──Type expr: Constructor: string
                               └──Type expr: Variable: a5795
                      └──Type expr: Constructor: unit
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: a5795
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: option
                            └──Type expr: Tuple
                               └──Type expr: Constructor: eq
                                  └──Type expr: Constructor: int
                                  └──Type expr: Variable: a5795
                               └──Type expr: Constructor: eq
                                  └──Type expr: Constructor: string
                                  └──Type expr: Variable: a5795
                         └──Type expr: Constructor: unit
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: option
                               └──Type expr: Tuple
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Constructor: int
                                     └──Type expr: Variable: a5795
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Constructor: string
                                     └──Type expr: Variable: a5795
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: unit
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Constructor: int
                                           └──Type expr: Variable: a5795
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Constructor: string
                                           └──Type expr: Variable: a5795
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: option
                                  └──Type expr: Tuple
                                     └──Type expr: Constructor: eq
                                        └──Type expr: Constructor: int
                                        └──Type expr: Variable: a5795
                                     └──Type expr: Constructor: eq
                                        └──Type expr: Constructor: string
                                        └──Type expr: Variable: a5795
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: option
                                           └──Type expr: Tuple
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Variable: a5795
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Constructor: string
                                                 └──Type expr: Variable: a5795
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: None
                                              └──Constructor type:
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Constructor: int
                                                          └──Type expr: Variable: a5795
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Constructor: string
                                                          └──Type expr: Variable: a5795
                                     └──Expression:
                                        └──Type expr: Constructor: unit
                                        └──Desc: Constant: () |}]