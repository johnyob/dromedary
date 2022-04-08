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
             └──Name: magic
             └──Scheme:
                └──Variables: a6975,a6974
                └──Type expr: Arrow
                   └──Type expr: Variable: a6974
                   └──Type expr: Variable: a6975
             └──Primitive name: %magic
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: a6983
                      └──Type expr: Arrow
                         └──Type expr: Variable: a6989
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: a6983
                            └──Type expr: Variable: a6989
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: a6983,a6989
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a6983
                         └──Type expr: Arrow
                            └──Type expr: Variable: a6989
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: a6983
                               └──Type expr: Variable: a6989
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a6983
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a6989
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: a6983
                                  └──Type expr: Variable: a6989
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: a6989
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: a6983
                                     └──Type expr: Variable: a6989
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: a7005
                                              └──Type expr: Variable: a7005
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: a6983
                                              └──Type expr: Variable: a6989
                                        └──Desc: Variable
                                           └──Variable: magic
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: a6983
                                              └──Type expr: Variable: a6989
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: a7005
                                              └──Type expr: Variable: a7005
                                     └──Expression:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: a7005
                                           └──Type expr: Variable: a7005
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Refl
                                              └──Constructor type:
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: a7005
                                                    └──Type expr: Variable: a7005
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: a7016
                      └──Type expr: Variable: a7016
                   └──Desc: Variable: of_type
                └──Abstraction:
                   └──Variables: a7016
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a7016
                         └──Type expr: Variable: a7016
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a7016
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: a7016
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: a7016
                                     └──Type expr: Constructor: int
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: a7016
                                              └──Type expr: Constructor: int
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: a7016
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a7016
                                                       └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: f
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Variable: a7016
                                           └──Expression:
                                              └──Type expr: Variable: a7016
                                              └──Desc: Variable
                                                 └──Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 4
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: a7016
                                  └──Type expr: Constructor: int
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: a7016
                                           └──Type expr: Constructor: int
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Refl
                                              └──Constructor type:
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: a7016
                                                    └──Type expr: Constructor: int
                                     └──Expression:
                                        └──Type expr: Variable: a7016
                                        └──Desc: Constant: 5 |}]