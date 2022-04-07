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
                └──Variables: a5558,a5557
                └──Type expr: Arrow
                   └──Type expr: Variable: a5557
                   └──Type expr: Variable: a5558
             └──Primitive name: %magic
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: a5566
                      └──Type expr: Arrow
                         └──Type expr: Variable: a5572
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: a5566
                            └──Type expr: Variable: a5572
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: a5566,a5572
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a5566
                         └──Type expr: Arrow
                            └──Type expr: Variable: a5572
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: a5566
                               └──Type expr: Variable: a5572
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a5566
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a5572
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: a5566
                                  └──Type expr: Variable: a5572
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: a5572
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: a5566
                                     └──Type expr: Variable: a5572
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: a5588
                                              └──Type expr: Variable: a5588
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: a5566
                                              └──Type expr: Variable: a5572
                                        └──Desc: Variable
                                           └──Variable: magic
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: a5566
                                              └──Type expr: Variable: a5572
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: a5588
                                              └──Type expr: Variable: a5588
                                     └──Expression:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: a5588
                                           └──Type expr: Variable: a5588
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Refl
                                              └──Constructor type:
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: a5588
                                                    └──Type expr: Variable: a5588
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: a5599
                      └──Type expr: Variable: a5599
                   └──Desc: Variable: of_type
                └──Abstraction:
                   └──Variables: a5599
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a5599
                         └──Type expr: Variable: a5599
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a5599
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: a5599
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: a5599
                                     └──Type expr: Constructor: int
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: a5599
                                              └──Type expr: Constructor: int
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: a5599
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a5599
                                                       └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: f
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Variable: a5599
                                           └──Expression:
                                              └──Type expr: Variable: a5599
                                              └──Desc: Variable
                                                 └──Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 4
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: a5599
                                  └──Type expr: Constructor: int
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: a5599
                                           └──Type expr: Constructor: int
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Refl
                                              └──Constructor type:
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: a5599
                                                    └──Type expr: Constructor: int
                                     └──Expression:
                                        └──Type expr: Variable: a5599
                                        └──Desc: Constant: 5 |}]