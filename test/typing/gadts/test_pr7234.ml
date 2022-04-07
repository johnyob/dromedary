open! Import
open Util

let%expect_test "" = 
  let str = 
    {|
      type ('a, 'b) cmp = 
        | Eq constraint 'a = 'b
        | Neq
      ;;

      type 'a t;;

      let (type 'a) f = 
        fun (t : ('a, 'a t) cmp) ->
          (match t with 
           ( Eq -> ()
           | Neq -> ()
           )
          : unit)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: cmp
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Eq
                   └──Constructor alphas: a b
                   └──Constructor type:
                      └──Type expr: Constructor: cmp
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Variable: b
                └──Constructor declaration:
                   └──Constructor name: Neq
                   └──Constructor alphas: a b
                   └──Constructor type:
                      └──Type expr: Constructor: cmp
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
       └──Structure item: Type
          └──Type declaration:
             └──Type name: t
             └──Type declaration kind: Abstract
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: cmp
                         └──Type expr: Variable: a5082
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a5082
                      └──Type expr: Constructor: unit
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: a5082
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: cmp
                            └──Type expr: Variable: a5082
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: a5082
                         └──Type expr: Constructor: unit
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: cmp
                               └──Type expr: Variable: a5082
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: a5082
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: unit
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: cmp
                                     └──Type expr: Variable: a5082
                                     └──Type expr: Constructor: t
                                        └──Type expr: Variable: a5082
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: cmp
                                  └──Type expr: Variable: a5082
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: a5082
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: cmp
                                           └──Type expr: Variable: a5082
                                           └──Type expr: Constructor: t
                                              └──Type expr: Variable: a5082
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Eq
                                              └──Constructor type:
                                                 └──Type expr: Constructor: cmp
                                                    └──Type expr: Variable: a5082
                                                    └──Type expr: Constructor: t
                                                       └──Type expr: Variable: a5082
                                     └──Expression:
                                        └──Type expr: Constructor: unit
                                        └──Desc: Constant: ()
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: cmp
                                           └──Type expr: Variable: a5082
                                           └──Type expr: Constructor: t
                                              └──Type expr: Variable: a5082
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Neq
                                              └──Constructor type:
                                                 └──Type expr: Constructor: cmp
                                                    └──Type expr: Variable: a5082
                                                    └──Type expr: Constructor: t
                                                       └──Type expr: Variable: a5082
                                     └──Expression:
                                        └──Type expr: Constructor: unit
                                        └──Desc: Constant: () |}]