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
                └──Variables: a16132,a16131
                └──Type expr: Arrow
                   └──Type expr: Variable: a16131
                   └──Type expr: Variable: a16132
             └──Primitive name: %magic
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: a16140
                      └──Type expr: Arrow
                         └──Type expr: Variable: a16146
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: a16140
                            └──Type expr: Variable: a16146
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: a16140,a16146
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a16140
                         └──Type expr: Arrow
                            └──Type expr: Variable: a16146
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: a16140
                               └──Type expr: Variable: a16146
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a16140
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a16146
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: a16140
                                  └──Type expr: Variable: a16146
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: a16146
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: a16140
                                     └──Type expr: Variable: a16146
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: a16162
                                              └──Type expr: Variable: a16162
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: a16140
                                              └──Type expr: Variable: a16146
                                        └──Desc: Variable
                                           └──Variable: magic
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: a16140
                                              └──Type expr: Variable: a16146
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: a16162
                                              └──Type expr: Variable: a16162
                                     └──Expression:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: a16162
                                           └──Type expr: Variable: a16162
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Refl
                                              └──Constructor type:
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: a16162
                                                    └──Type expr: Variable: a16162
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: a16173
                      └──Type expr: Variable: a16173
                   └──Desc: Variable: of_type
                └──Abstraction:
                   └──Variables: a16173
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a16173
                         └──Type expr: Variable: a16173
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a16173
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: a16173
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: a16173
                                     └──Type expr: Constructor: int
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: a16173
                                              └──Type expr: Constructor: int
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: a16173
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a16173
                                                       └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: f
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Variable: a16173
                                           └──Expression:
                                              └──Type expr: Variable: a16173
                                              └──Desc: Variable
                                                 └──Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 4
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: a16173
                                  └──Type expr: Constructor: int
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: a16173
                                           └──Type expr: Constructor: int
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Refl
                                              └──Constructor type:
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: a16173
                                                    └──Type expr: Constructor: int
                                     └──Expression:
                                        └──Type expr: Variable: a16173
                                        └──Desc: Constant: 5 |}]