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
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: t
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: ctx tl
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: ctx
                         └──Type expr: Variable: tl
                   └──Constraint:
                      └──Type expr: Variable: ctx
                      └──Type expr: Variable: tl
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: ctx tl
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: ctx
                         └──Type expr: Variable: tl
                   └──Constructor argument:
                      └──Constructor betas: a b
                      └──Type expr: Tuple
                         └──Type expr: Variable: a
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: b
                            └──Type expr: Variable: tl
                   └──Constraint:
                      └──Type expr: Variable: ctx
                      └──Type expr: Tuple
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Tuple
                            └──Type expr: Variable: a15133
                            └──Type expr: Variable: a15134
                         └──Type expr: Variable: a15134
                      └──Type expr: Variable: a15133
                   └──Desc: Variable: get1
                └──Abstraction:
                   └──Variables: a15134,a15133
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Tuple
                               └──Type expr: Variable: a15133
                               └──Type expr: Variable: a15134
                            └──Type expr: Variable: a15134
                         └──Type expr: Variable: a15133
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Tuple
                                  └──Type expr: Variable: a15133
                                  └──Type expr: Variable: a15134
                               └──Type expr: Variable: a15134
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Cons
                                  └──Constructor argument type:
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a15136
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: a15138
                                           └──Type expr: Variable: a15134
                                  └──Constructor type:
                                     └──Type expr: Constructor: t
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a15133
                                           └──Type expr: Variable: a15134
                                        └──Type expr: Variable: a15134
                               └──Pattern:
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: a15136
                                     └──Type expr: Constructor: t
                                        └──Type expr: Variable: a15138
                                        └──Type expr: Variable: a15134
                                  └──Desc: Tuple
                                     └──Pattern:
                                        └──Type expr: Variable: a15136
                                        └──Desc: Variable: x
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: a15138
                                           └──Type expr: Variable: a15134
                                        └──Desc: Any
                         └──Expression:
                            └──Type expr: Variable: a15133
                            └──Desc: Variable
                               └──Variable: x |}]