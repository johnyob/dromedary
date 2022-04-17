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
                   └──Constructor alphas: 15675 15676
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 15675
                         └──Type expr: Variable: 15676
                   └──Constraint:
                      └──Type expr: Variable: 15675
                      └──Type expr: Variable: 15676
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 15675 15676
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 15675
                         └──Type expr: Variable: 15676
                   └──Constructor argument:
                      └──Constructor betas: 15679 15678
                      └──Type expr: Tuple
                         └──Type expr: Variable: 15678
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: 15679
                            └──Type expr: Variable: 15676
                   └──Constraint:
                      └──Type expr: Variable: 15675
                      └──Type expr: Tuple
                         └──Type expr: Variable: 15678
                         └──Type expr: Variable: 15679
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Tuple
                            └──Type expr: Variable: 15707
                            └──Type expr: Variable: 15708
                         └──Type expr: Variable: 15708
                      └──Type expr: Variable: 15707
                   └──Desc: Variable: get1
                └──Abstraction:
                   └──Variables: 15708,15707
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Tuple
                               └──Type expr: Variable: 15707
                               └──Type expr: Variable: 15708
                            └──Type expr: Variable: 15708
                         └──Type expr: Variable: 15707
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Tuple
                                  └──Type expr: Variable: 15707
                                  └──Type expr: Variable: 15708
                               └──Type expr: Variable: 15708
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Cons
                                  └──Constructor argument type:
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: 15710
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: 15712
                                           └──Type expr: Variable: 15708
                                  └──Constructor type:
                                     └──Type expr: Constructor: t
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 15707
                                           └──Type expr: Variable: 15708
                                        └──Type expr: Variable: 15708
                               └──Pattern:
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: 15710
                                     └──Type expr: Constructor: t
                                        └──Type expr: Variable: 15712
                                        └──Type expr: Variable: 15708
                                  └──Desc: Tuple
                                     └──Pattern:
                                        └──Type expr: Variable: 15710
                                        └──Desc: Variable: x
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: 15712
                                           └──Type expr: Variable: 15708
                                        └──Desc: Any
                         └──Expression:
                            └──Type expr: Variable: 15707
                            └──Desc: Variable
                               └──Variable: x |}]