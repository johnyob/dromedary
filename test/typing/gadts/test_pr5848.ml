open! Import
open Util

let%expect_test "" = 
  let str = 
    {|
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      external magic : 'a 'b. 'a -> 'b = "%magic";;

      let (type 'a 'b) f = 
        fun (t1 : 'a) (t2 : 'b) ->
          (magic Refl : ('a, 'b) eq)
      ;;

      let (type 'a) of_type = 
        fun (x : 'a) ->
          (match f x 4 with ( Refl -> 5 ) : 'a)
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
                   └──Constructor alphas: 383 384
                   └──Constructor type:
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: 383
                         └──Type expr: Variable: 384
                   └──Constraint:
                      └──Type expr: Variable: 383
                      └──Type expr: Variable: 384
       └──Structure item: Primitive
          └──Value description:
             └──Name: magic
             └──Scheme:
                └──Variables: 1,0
                └──Type expr: Arrow
                   └──Type expr: Variable: 0
                   └──Type expr: Variable: 1
             └──Primitive name: %magic
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 9
                      └──Type expr: Arrow
                         └──Type expr: Variable: 15
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: 9
                            └──Type expr: Variable: 15
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: 9,15
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 9
                         └──Type expr: Arrow
                            └──Type expr: Variable: 15
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: 9
                               └──Type expr: Variable: 15
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 9
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: 15
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: 9
                                  └──Type expr: Variable: 15
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: 15
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: 9
                                     └──Type expr: Variable: 15
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: 31
                                              └──Type expr: Variable: 31
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: 9
                                              └──Type expr: Variable: 15
                                        └──Desc: Variable
                                           └──Variable: magic
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: 9
                                              └──Type expr: Variable: 15
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: 31
                                              └──Type expr: Variable: 31
                                     └──Expression:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: 31
                                           └──Type expr: Variable: 31
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Refl
                                              └──Constructor type:
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: 31
                                                    └──Type expr: Variable: 31
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 42
                      └──Type expr: Variable: 42
                   └──Desc: Variable: of_type
                └──Abstraction:
                   └──Variables: 42
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 42
                         └──Type expr: Variable: 42
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 42
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: 42
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: 42
                                     └──Type expr: Constructor: int
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: 42
                                              └──Type expr: Constructor: int
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: 42
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: 42
                                                       └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: f
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Variable: 42
                                           └──Expression:
                                              └──Type expr: Variable: 42
                                              └──Desc: Variable
                                                 └──Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 4
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: 42
                                  └──Type expr: Constructor: int
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: 42
                                           └──Type expr: Constructor: int
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Refl
                                              └──Constructor type:
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: 42
                                                    └──Type expr: Constructor: int
                                     └──Expression:
                                        └──Type expr: Variable: 42
                                        └──Desc: Constant: 5 |}]