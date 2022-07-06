open! Import
open Util

let%expect_test "" = 
  let str = 
    {|
      type empty = Empty;;
      type filled = Filled;;

      type ('a, 'fout, 'fin) option = 
        | None constraint 'fin = 'fout
        | Some of 'a constraint 'fout = filled and 'fin = empty
      ;;

      type 'fill either = 
        | Either of 'f. (string, 'fill, 'f) option * (int, 'f, empty) option
      ;;
      
      let (type 'fill) f = 
        fun (Either (Some a, None) : 'fill either) ->
          a
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: empty
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Empty
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: empty
       └──Structure item: Type
          └──Type declaration:
             └──Type name: filled
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Filled
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: filled
       └──Structure item: Type
          └──Type declaration:
             └──Type name: option
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: None
                   └──Constructor alphas: 33 34 35
                   └──Constructor type:
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: 33
                         └──Type expr: Variable: 34
                         └──Type expr: Variable: 35
                   └──Constraint:
                      └──Type expr: Variable: 35
                      └──Type expr: Variable: 34
                └──Constructor declaration:
                   └──Constructor name: Some
                   └──Constructor alphas: 33 34 35
                   └──Constructor type:
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: 33
                         └──Type expr: Variable: 34
                         └──Type expr: Variable: 35
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: 33
                   └──Constraint:
                      └──Type expr: Variable: 34
                      └──Type expr: Constructor: filled
                   └──Constraint:
                      └──Type expr: Variable: 35
                      └──Type expr: Constructor: empty
       └──Structure item: Type
          └──Type declaration:
             └──Type name: either
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Either
                   └──Constructor alphas: 40
                   └──Constructor type:
                      └──Type expr: Constructor: either
                         └──Type expr: Variable: 40
                   └──Constructor argument:
                      └──Constructor betas: 41
                      └──Type expr: Tuple
                         └──Type expr: Constructor: option
                            └──Type expr: Constructor: string
                            └──Type expr: Variable: 40
                            └──Type expr: Variable: 41
                         └──Type expr: Constructor: option
                            └──Type expr: Constructor: int
                            └──Type expr: Variable: 41
                            └──Type expr: Constructor: empty
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: either
                         └──Type expr: Variable: 22
                      └──Type expr: Constructor: string
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: 22
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: either
                            └──Type expr: Variable: 22
                         └──Type expr: Constructor: string
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: either
                               └──Type expr: Variable: 22
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Either
                                  └──Constructor argument type:
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: option
                                           └──Type expr: Constructor: string
                                           └──Type expr: Variable: 22
                                           └──Type expr: Variable: 23
                                        └──Type expr: Constructor: option
                                           └──Type expr: Constructor: int
                                           └──Type expr: Variable: 23
                                           └──Type expr: Constructor: empty
                                  └──Constructor type:
                                     └──Type expr: Constructor: either
                                        └──Type expr: Variable: 22
                               └──Pattern:
                                  └──Type expr: Tuple
                                     └──Type expr: Constructor: option
                                        └──Type expr: Constructor: string
                                        └──Type expr: Variable: 22
                                        └──Type expr: Variable: 23
                                     └──Type expr: Constructor: option
                                        └──Type expr: Constructor: int
                                        └──Type expr: Variable: 23
                                        └──Type expr: Constructor: empty
                                  └──Desc: Tuple
                                     └──Pattern:
                                        └──Type expr: Constructor: option
                                           └──Type expr: Constructor: string
                                           └──Type expr: Variable: 22
                                           └──Type expr: Variable: 23
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Some
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: string
                                              └──Constructor type:
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Constructor: string
                                                    └──Type expr: Variable: 22
                                                    └──Type expr: Variable: 23
                                           └──Pattern:
                                              └──Type expr: Constructor: string
                                              └──Desc: Variable: a
                                     └──Pattern:
                                        └──Type expr: Constructor: option
                                           └──Type expr: Constructor: int
                                           └──Type expr: Variable: 23
                                           └──Type expr: Constructor: empty
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: None
                                              └──Constructor type:
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Variable: 23
                                                    └──Type expr: Constructor: empty
                         └──Expression:
                            └──Type expr: Constructor: string
                            └──Desc: Variable
                               └──Variable: a |}]