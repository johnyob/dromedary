open! Import
open Util

let%expect_test "" = 
  let str = 
    {|
      type 'a t = 
        | Int of int constraint 'a = int
        | String of string constraint 'a = string
        | Same of 'a t
      ;;

      let rec f = 
        fun (t : int t) ->
          (match t with
           ( Int x -> x
           | Same t -> f t
           ) 
          : int)
      ;;

      (* definition of [tt] not supported -- do not support manifest types *)
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
                   └──Constructor name: Int
                   └──Constructor alphas: 15604
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 15604
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: int
                   └──Constraint:
                      └──Type expr: Variable: 15604
                      └──Type expr: Constructor: int
                └──Constructor declaration:
                   └──Constructor name: String
                   └──Constructor alphas: 15604
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 15604
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: string
                   └──Constraint:
                      └──Type expr: Variable: 15604
                      └──Type expr: Constructor: string
                └──Constructor declaration:
                   └──Constructor name: Same
                   └──Constructor alphas: 15604
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 15604
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 15604
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: f
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Constructor: int
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Constructor: int
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: t
                                  └──Type expr: Constructor: int
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Constructor: int
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Int
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: int
                                              └──Constructor type:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Constructor: int
                                           └──Pattern:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Variable
                                           └──Variable: x
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Constructor: int
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Same
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Constructor: int
                                              └──Constructor type:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Constructor: int
                                           └──Pattern:
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Constructor: int
                                              └──Desc: Variable: t
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: f
                                           └──Expression:
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: t |}]