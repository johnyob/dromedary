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
                   └──Constructor alphas: a fout fin
                   └──Constructor type:
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: a
                         └──Type expr: Variable: fout
                         └──Type expr: Variable: fin
                   └──Constraint:
                      └──Type expr: Variable: fin
                      └──Type expr: Variable: fout
                └──Constructor declaration:
                   └──Constructor name: Some
                   └──Constructor alphas: a fout fin
                   └──Constructor type:
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: a
                         └──Type expr: Variable: fout
                         └──Type expr: Variable: fin
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: fout
                      └──Type expr: Constructor: filled
                   └──Constraint:
                      └──Type expr: Variable: fin
                      └──Type expr: Constructor: empty
       └──Structure item: Type
          └──Type declaration:
             └──Type name: either
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Either
                   └──Constructor alphas: fill
                   └──Constructor type:
                      └──Type expr: Constructor: either
                         └──Type expr: Variable: fill
                   └──Constructor argument:
                      └──Constructor betas: f
                      └──Type expr: Tuple
                         └──Type expr: Constructor: option
                            └──Type expr: Constructor: string
                            └──Type expr: Variable: fill
                            └──Type expr: Variable: f
                         └──Type expr: Constructor: option
                            └──Type expr: Constructor: int
                            └──Type expr: Variable: f
                            └──Type expr: Constructor: empty
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: either
                         └──Type expr: Variable: a14846
                      └──Type expr: Constructor: string
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: a14846
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: either
                            └──Type expr: Variable: a14846
                         └──Type expr: Constructor: string
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: either
                               └──Type expr: Variable: a14846
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Either
                                  └──Constructor argument type:
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: option
                                           └──Type expr: Constructor: string
                                           └──Type expr: Variable: a14846
                                           └──Type expr: Variable: a14845
                                        └──Type expr: Constructor: option
                                           └──Type expr: Constructor: int
                                           └──Type expr: Variable: a14845
                                           └──Type expr: Constructor: empty
                                  └──Constructor type:
                                     └──Type expr: Constructor: either
                                        └──Type expr: Variable: a14846
                               └──Pattern:
                                  └──Type expr: Tuple
                                     └──Type expr: Constructor: option
                                        └──Type expr: Constructor: string
                                        └──Type expr: Variable: a14846
                                        └──Type expr: Variable: a14845
                                     └──Type expr: Constructor: option
                                        └──Type expr: Constructor: int
                                        └──Type expr: Variable: a14845
                                        └──Type expr: Constructor: empty
                                  └──Desc: Tuple
                                     └──Pattern:
                                        └──Type expr: Constructor: option
                                           └──Type expr: Constructor: string
                                           └──Type expr: Variable: a14846
                                           └──Type expr: Variable: a14845
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Some
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: string
                                              └──Constructor type:
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Constructor: string
                                                    └──Type expr: Variable: a14846
                                                    └──Type expr: Variable: a14845
                                           └──Pattern:
                                              └──Type expr: Constructor: string
                                              └──Desc: Variable: a
                                     └──Pattern:
                                        └──Type expr: Constructor: option
                                           └──Type expr: Constructor: int
                                           └──Type expr: Variable: a14845
                                           └──Type expr: Constructor: empty
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: None
                                              └──Constructor type:
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Variable: a14845
                                                    └──Type expr: Constructor: empty
                         └──Expression:
                            └──Type expr: Constructor: string
                            └──Desc: Variable
                               └──Variable: a |}]