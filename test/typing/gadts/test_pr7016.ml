open! Import
open Util

let%expect_test "" =
  let str =
    {|
      type ('ctx, 'tl) t = 
        | Nil constraint 'ctx = 'tl
        | Cons of 'a 'b. 'a * ('b, 'tl) t constraint 'ctx = 'a * 'b
      ;;

      let (type 'b 'a) get1 = 
        fun (Cons (x, _) : ('b * 'a, 'a) t) -> (x : 'b)
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
             └──Type name: t
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: 62 63
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 62
                         └──Type expr: Variable: 63
                   └──Constraint:
                      └──Type expr: Variable: 62
                      └──Type expr: Variable: 63
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 62 63
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 62
                         └──Type expr: Variable: 63
                   └──Constructor argument:
                      └──Constructor betas: 66 65
                      └──Type expr: Tuple
                         └──Type expr: Variable: 65
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: 66
                            └──Type expr: Variable: 63
                   └──Constraint:
                      └──Type expr: Variable: 62
                      └──Type expr: Tuple
                         └──Type expr: Variable: 65
                         └──Type expr: Variable: 66
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Tuple
                            └──Type expr: Variable: 23
                            └──Type expr: Variable: 24
                         └──Type expr: Variable: 24
                      └──Type expr: Variable: 23
                   └──Desc: Variable: get1
                └──Abstraction:
                   └──Variables: 24,23
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Tuple
                               └──Type expr: Variable: 23
                               └──Type expr: Variable: 24
                            └──Type expr: Variable: 24
                         └──Type expr: Variable: 23
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Tuple
                                  └──Type expr: Variable: 23
                                  └──Type expr: Variable: 24
                               └──Type expr: Variable: 24
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Cons
                                  └──Constructor argument type:
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: 26
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: 28
                                           └──Type expr: Variable: 24
                                  └──Constructor type:
                                     └──Type expr: Constructor: t
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 23
                                           └──Type expr: Variable: 24
                                        └──Type expr: Variable: 24
                               └──Pattern:
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: 26
                                     └──Type expr: Constructor: t
                                        └──Type expr: Variable: 28
                                        └──Type expr: Variable: 24
                                  └──Desc: Tuple
                                     └──Pattern:
                                        └──Type expr: Variable: 26
                                        └──Desc: Variable: x
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: 28
                                           └──Type expr: Variable: 24
                                        └──Desc: Any
                         └──Expression:
                            └──Type expr: Variable: 23
                            └──Desc: Variable
                               └──Variable: x |}]
