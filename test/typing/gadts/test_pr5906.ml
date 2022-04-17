open! Import
open Util

let%expect_test "" = 
  let str = 
    {|
      type 'a constant = 
        | Int of int constraint 'a = int
        | Bool of bool constraint 'a = bool
      ;;

      type ('a, 'b, 'c) bin_op = 
        | Eq constraint 'a = 'b and 'c = bool
        | Leq constraint 'a = 'b and 'c = bool
        | Add constraint 'a = int and 'b = int and 'c = int
      ;;

      external bool_eq : bool -> bool -> bool = "%bool_eq";;
      external bool_leq : bool -> bool -> bool = "%bool_leq";;
      external leq : int -> int -> bool = "%leq";;

      let (type 'a 'b 'c) eval = 
        fun (bop : ('a, 'b, 'c) bin_op) (x : 'a constant) (y : 'b constant) ->
          (match (bop, x, y) with 
           ( (Eq, Bool x, Bool y) -> Bool (bool_eq x y)
           | (Eq, Int x, Int y) -> Bool (x = y)
           | (Leq, Int x, Int y) -> Bool (leq x y)
           | (Leq, Bool x, Bool y) -> Bool (bool_leq x y)
           | (Add, Int x, Int y) -> Int (x + y)
           )
          : 'c constant)
      ;;

      let _ = eval Eq (Int 2) (Int 3);;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: constant
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Int
                   └──Constructor alphas: 16422
                   └──Constructor type:
                      └──Type expr: Constructor: constant
                         └──Type expr: Variable: 16422
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: int
                   └──Constraint:
                      └──Type expr: Variable: 16422
                      └──Type expr: Constructor: int
                └──Constructor declaration:
                   └──Constructor name: Bool
                   └──Constructor alphas: 16422
                   └──Constructor type:
                      └──Type expr: Constructor: constant
                         └──Type expr: Variable: 16422
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: bool
                   └──Constraint:
                      └──Type expr: Variable: 16422
                      └──Type expr: Constructor: bool
       └──Structure item: Type
          └──Type declaration:
             └──Type name: bin_op
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Eq
                   └──Constructor alphas: 16429 16430 16431
                   └──Constructor type:
                      └──Type expr: Constructor: bin_op
                         └──Type expr: Variable: 16429
                         └──Type expr: Variable: 16430
                         └──Type expr: Variable: 16431
                   └──Constraint:
                      └──Type expr: Variable: 16429
                      └──Type expr: Variable: 16430
                   └──Constraint:
                      └──Type expr: Variable: 16431
                      └──Type expr: Constructor: bool
                └──Constructor declaration:
                   └──Constructor name: Leq
                   └──Constructor alphas: 16429 16430 16431
                   └──Constructor type:
                      └──Type expr: Constructor: bin_op
                         └──Type expr: Variable: 16429
                         └──Type expr: Variable: 16430
                         └──Type expr: Variable: 16431
                   └──Constraint:
                      └──Type expr: Variable: 16429
                      └──Type expr: Variable: 16430
                   └──Constraint:
                      └──Type expr: Variable: 16431
                      └──Type expr: Constructor: bool
                └──Constructor declaration:
                   └──Constructor name: Add
                   └──Constructor alphas: 16429 16430 16431
                   └──Constructor type:
                      └──Type expr: Constructor: bin_op
                         └──Type expr: Variable: 16429
                         └──Type expr: Variable: 16430
                         └──Type expr: Variable: 16431
                   └──Constraint:
                      └──Type expr: Variable: 16429
                      └──Type expr: Constructor: int
                   └──Constraint:
                      └──Type expr: Variable: 16430
                      └──Type expr: Constructor: int
                   └──Constraint:
                      └──Type expr: Variable: 16431
                      └──Type expr: Constructor: int
       └──Structure item: Primitive
          └──Value description:
             └──Name: bool_eq
             └──Scheme:
                └──Variables:
                └──Type expr: Arrow
                   └──Type expr: Constructor: bool
                   └──Type expr: Arrow
                      └──Type expr: Constructor: bool
                      └──Type expr: Constructor: bool
             └──Primitive name: %bool_eq
       └──Structure item: Primitive
          └──Value description:
             └──Name: bool_leq
             └──Scheme:
                └──Variables:
                └──Type expr: Arrow
                   └──Type expr: Constructor: bool
                   └──Type expr: Arrow
                      └──Type expr: Constructor: bool
                      └──Type expr: Constructor: bool
             └──Primitive name: %bool_leq
       └──Structure item: Primitive
          └──Value description:
             └──Name: leq
             └──Scheme:
                └──Variables:
                └──Type expr: Arrow
                   └──Type expr: Constructor: int
                   └──Type expr: Arrow
                      └──Type expr: Constructor: int
                      └──Type expr: Constructor: bool
             └──Primitive name: %leq
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: bin_op
                         └──Type expr: Variable: 16481
                         └──Type expr: Variable: 16482
                         └──Type expr: Variable: 16483
                      └──Type expr: Arrow
                         └──Type expr: Constructor: constant
                            └──Type expr: Variable: 16481
                         └──Type expr: Arrow
                            └──Type expr: Constructor: constant
                               └──Type expr: Variable: 16482
                            └──Type expr: Constructor: constant
                               └──Type expr: Variable: 16483
                   └──Desc: Variable: eval
                └──Abstraction:
                   └──Variables: 16481,16482,16483
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: bin_op
                            └──Type expr: Variable: 16481
                            └──Type expr: Variable: 16482
                            └──Type expr: Variable: 16483
                         └──Type expr: Arrow
                            └──Type expr: Constructor: constant
                               └──Type expr: Variable: 16481
                            └──Type expr: Arrow
                               └──Type expr: Constructor: constant
                                  └──Type expr: Variable: 16482
                               └──Type expr: Constructor: constant
                                  └──Type expr: Variable: 16483
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: bin_op
                               └──Type expr: Variable: 16481
                               └──Type expr: Variable: 16482
                               └──Type expr: Variable: 16483
                            └──Desc: Variable: bop
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: constant
                                  └──Type expr: Variable: 16481
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: constant
                                     └──Type expr: Variable: 16482
                                  └──Type expr: Constructor: constant
                                     └──Type expr: Variable: 16483
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: constant
                                     └──Type expr: Variable: 16481
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: constant
                                        └──Type expr: Variable: 16482
                                     └──Type expr: Constructor: constant
                                        └──Type expr: Variable: 16483
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: constant
                                           └──Type expr: Variable: 16482
                                        └──Desc: Variable: y
                                     └──Expression:
                                        └──Type expr: Constructor: constant
                                           └──Type expr: Variable: 16483
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: bin_op
                                                    └──Type expr: Variable: 16481
                                                    └──Type expr: Variable: 16482
                                                    └──Type expr: Variable: 16483
                                                 └──Type expr: Constructor: constant
                                                    └──Type expr: Variable: 16481
                                                 └──Type expr: Constructor: constant
                                                    └──Type expr: Variable: 16482
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: bin_op
                                                       └──Type expr: Variable: 16481
                                                       └──Type expr: Variable: 16482
                                                       └──Type expr: Variable: 16483
                                                    └──Desc: Variable
                                                       └──Variable: bop
                                                 └──Expression:
                                                    └──Type expr: Constructor: constant
                                                       └──Type expr: Variable: 16481
                                                    └──Desc: Variable
                                                       └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: constant
                                                       └──Type expr: Variable: 16482
                                                    └──Desc: Variable
                                                       └──Variable: y
                                           └──Type expr: Tuple
                                              └──Type expr: Constructor: bin_op
                                                 └──Type expr: Variable: 16481
                                                 └──Type expr: Variable: 16482
                                                 └──Type expr: Variable: 16483
                                              └──Type expr: Constructor: constant
                                                 └──Type expr: Variable: 16481
                                              └──Type expr: Constructor: constant
                                                 └──Type expr: Variable: 16482
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: bin_op
                                                          └──Type expr: Variable: 16481
                                                          └──Type expr: Variable: 16482
                                                          └──Type expr: Variable: 16483
                                                       └──Type expr: Constructor: constant
                                                          └──Type expr: Variable: 16481
                                                       └──Type expr: Constructor: constant
                                                          └──Type expr: Variable: 16482
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: bin_op
                                                             └──Type expr: Variable: 16481
                                                             └──Type expr: Variable: 16482
                                                             └──Type expr: Variable: 16483
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Eq
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: bin_op
                                                                      └──Type expr: Variable: 16481
                                                                      └──Type expr: Variable: 16482
                                                                      └──Type expr: Variable: 16483
                                                       └──Pattern:
                                                          └──Type expr: Constructor: constant
                                                             └──Type expr: Variable: 16481
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Bool
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: bool
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: constant
                                                                      └──Type expr: Variable: 16481
                                                             └──Pattern:
                                                                └──Type expr: Constructor: bool
                                                                └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: constant
                                                             └──Type expr: Variable: 16482
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Bool
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: bool
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: constant
                                                                      └──Type expr: Variable: 16482
                                                             └──Pattern:
                                                                └──Type expr: Constructor: bool
                                                                └──Desc: Variable: y
                                                 └──Expression:
                                                    └──Type expr: Constructor: constant
                                                       └──Type expr: Variable: 16483
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Bool
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: bool
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: constant
                                                                └──Type expr: Variable: 16483
                                                       └──Expression:
                                                          └──Type expr: Constructor: bool
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: bool
                                                                   └──Type expr: Constructor: bool
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: bool
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: bool
                                                                            └──Type expr: Constructor: bool
                                                                      └──Desc: Variable
                                                                         └──Variable: bool_eq
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: bool
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: bool
                                                                └──Desc: Variable
                                                                   └──Variable: y
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: bin_op
                                                          └──Type expr: Variable: 16481
                                                          └──Type expr: Variable: 16482
                                                          └──Type expr: Variable: 16483
                                                       └──Type expr: Constructor: constant
                                                          └──Type expr: Variable: 16481
                                                       └──Type expr: Constructor: constant
                                                          └──Type expr: Variable: 16482
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: bin_op
                                                             └──Type expr: Variable: 16481
                                                             └──Type expr: Variable: 16482
                                                             └──Type expr: Variable: 16483
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Eq
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: bin_op
                                                                      └──Type expr: Variable: 16481
                                                                      └──Type expr: Variable: 16482
                                                                      └──Type expr: Variable: 16483
                                                       └──Pattern:
                                                          └──Type expr: Constructor: constant
                                                             └──Type expr: Variable: 16481
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Int
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: int
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: constant
                                                                      └──Type expr: Variable: 16481
                                                             └──Pattern:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: constant
                                                             └──Type expr: Variable: 16482
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Int
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: int
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: constant
                                                                      └──Type expr: Variable: 16482
                                                             └──Pattern:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable: y
                                                 └──Expression:
                                                    └──Type expr: Constructor: constant
                                                       └──Type expr: Variable: 16483
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Bool
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: bool
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: constant
                                                                └──Type expr: Variable: 16483
                                                       └──Expression:
                                                          └──Type expr: Constructor: bool
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: int
                                                                   └──Type expr: Constructor: bool
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: int
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: int
                                                                            └──Type expr: Constructor: bool
                                                                      └──Desc: Primitive: (=)
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: y
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: bin_op
                                                          └──Type expr: Variable: 16481
                                                          └──Type expr: Variable: 16482
                                                          └──Type expr: Variable: 16483
                                                       └──Type expr: Constructor: constant
                                                          └──Type expr: Variable: 16481
                                                       └──Type expr: Constructor: constant
                                                          └──Type expr: Variable: 16482
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: bin_op
                                                             └──Type expr: Variable: 16481
                                                             └──Type expr: Variable: 16482
                                                             └──Type expr: Variable: 16483
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Leq
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: bin_op
                                                                      └──Type expr: Variable: 16481
                                                                      └──Type expr: Variable: 16482
                                                                      └──Type expr: Variable: 16483
                                                       └──Pattern:
                                                          └──Type expr: Constructor: constant
                                                             └──Type expr: Variable: 16481
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Int
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: int
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: constant
                                                                      └──Type expr: Variable: 16481
                                                             └──Pattern:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: constant
                                                             └──Type expr: Variable: 16482
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Int
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: int
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: constant
                                                                      └──Type expr: Variable: 16482
                                                             └──Pattern:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable: y
                                                 └──Expression:
                                                    └──Type expr: Constructor: constant
                                                       └──Type expr: Variable: 16483
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Bool
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: bool
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: constant
                                                                └──Type expr: Variable: 16483
                                                       └──Expression:
                                                          └──Type expr: Constructor: bool
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: int
                                                                   └──Type expr: Constructor: bool
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: int
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: int
                                                                            └──Type expr: Constructor: bool
                                                                      └──Desc: Variable
                                                                         └──Variable: leq
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: y
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: bin_op
                                                          └──Type expr: Variable: 16481
                                                          └──Type expr: Variable: 16482
                                                          └──Type expr: Variable: 16483
                                                       └──Type expr: Constructor: constant
                                                          └──Type expr: Variable: 16481
                                                       └──Type expr: Constructor: constant
                                                          └──Type expr: Variable: 16482
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: bin_op
                                                             └──Type expr: Variable: 16481
                                                             └──Type expr: Variable: 16482
                                                             └──Type expr: Variable: 16483
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Leq
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: bin_op
                                                                      └──Type expr: Variable: 16481
                                                                      └──Type expr: Variable: 16482
                                                                      └──Type expr: Variable: 16483
                                                       └──Pattern:
                                                          └──Type expr: Constructor: constant
                                                             └──Type expr: Variable: 16481
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Bool
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: bool
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: constant
                                                                      └──Type expr: Variable: 16481
                                                             └──Pattern:
                                                                └──Type expr: Constructor: bool
                                                                └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: constant
                                                             └──Type expr: Variable: 16482
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Bool
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: bool
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: constant
                                                                      └──Type expr: Variable: 16482
                                                             └──Pattern:
                                                                └──Type expr: Constructor: bool
                                                                └──Desc: Variable: y
                                                 └──Expression:
                                                    └──Type expr: Constructor: constant
                                                       └──Type expr: Variable: 16483
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Bool
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: bool
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: constant
                                                                └──Type expr: Variable: 16483
                                                       └──Expression:
                                                          └──Type expr: Constructor: bool
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: bool
                                                                   └──Type expr: Constructor: bool
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: bool
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: bool
                                                                            └──Type expr: Constructor: bool
                                                                      └──Desc: Variable
                                                                         └──Variable: bool_leq
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: bool
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: bool
                                                                └──Desc: Variable
                                                                   └──Variable: y
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: bin_op
                                                          └──Type expr: Variable: 16481
                                                          └──Type expr: Variable: 16482
                                                          └──Type expr: Variable: 16483
                                                       └──Type expr: Constructor: constant
                                                          └──Type expr: Variable: 16481
                                                       └──Type expr: Constructor: constant
                                                          └──Type expr: Variable: 16482
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: bin_op
                                                             └──Type expr: Variable: 16481
                                                             └──Type expr: Variable: 16482
                                                             └──Type expr: Variable: 16483
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Add
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: bin_op
                                                                      └──Type expr: Variable: 16481
                                                                      └──Type expr: Variable: 16482
                                                                      └──Type expr: Variable: 16483
                                                       └──Pattern:
                                                          └──Type expr: Constructor: constant
                                                             └──Type expr: Variable: 16481
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Int
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: int
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: constant
                                                                      └──Type expr: Variable: 16481
                                                             └──Pattern:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: constant
                                                             └──Type expr: Variable: 16482
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Int
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: int
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: constant
                                                                      └──Type expr: Variable: 16482
                                                             └──Pattern:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable: y
                                                 └──Expression:
                                                    └──Type expr: Constructor: constant
                                                       └──Type expr: Variable: 16483
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Int
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: constant
                                                                └──Type expr: Variable: 16483
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: int
                                                                   └──Type expr: Constructor: int
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: int
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: int
                                                                            └──Type expr: Constructor: int
                                                                      └──Desc: Primitive: (+)
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: y
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: constant
                      └──Type expr: Constructor: bool
                   └──Desc: Any
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: constant
                         └──Type expr: Constructor: bool
                      └──Desc: Application
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: constant
                                  └──Type expr: Constructor: int
                               └──Type expr: Constructor: constant
                                  └──Type expr: Constructor: bool
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: constant
                                        └──Type expr: Constructor: int
                                     └──Type expr: Arrow
                                        └──Type expr: Constructor: constant
                                           └──Type expr: Constructor: int
                                        └──Type expr: Constructor: constant
                                           └──Type expr: Constructor: bool
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: bin_op
                                              └──Type expr: Constructor: int
                                              └──Type expr: Constructor: int
                                              └──Type expr: Constructor: bool
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: constant
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: constant
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: constant
                                                    └──Type expr: Constructor: bool
                                        └──Desc: Variable
                                           └──Variable: eval
                                           └──Type expr: Constructor: bool
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: int
                                     └──Expression:
                                        └──Type expr: Constructor: bin_op
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: bool
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Eq
                                              └──Constructor type:
                                                 └──Type expr: Constructor: bin_op
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: bool
                               └──Expression:
                                  └──Type expr: Constructor: constant
                                     └──Type expr: Constructor: int
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Int
                                        └──Constructor argument type:
                                           └──Type expr: Constructor: int
                                        └──Constructor type:
                                           └──Type expr: Constructor: constant
                                              └──Type expr: Constructor: int
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 2
                         └──Expression:
                            └──Type expr: Constructor: constant
                               └──Type expr: Constructor: int
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Int
                                  └──Constructor argument type:
                                     └──Type expr: Constructor: int
                                  └──Constructor type:
                                     └──Type expr: Constructor: constant
                                        └──Type expr: Constructor: int
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Constant: 3 |}]