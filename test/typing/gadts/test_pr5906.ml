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
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: constant
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Int
                   └──Constructor alphas: 54
                   └──Constructor type:
                      └──Type expr: Constructor: constant
                         └──Type expr: Variable: 54
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: int
                   └──Constraint:
                      └──Type expr: Variable: 54
                      └──Type expr: Constructor: int
                └──Constructor declaration:
                   └──Constructor name: Bool
                   └──Constructor alphas: 54
                   └──Constructor type:
                      └──Type expr: Constructor: constant
                         └──Type expr: Variable: 54
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: bool
                   └──Constraint:
                      └──Type expr: Variable: 54
                      └──Type expr: Constructor: bool
       └──Structure item: Type
          └──Type declaration:
             └──Type name: bin_op
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Eq
                   └──Constructor alphas: 61 62 63
                   └──Constructor type:
                      └──Type expr: Constructor: bin_op
                         └──Type expr: Variable: 61
                         └──Type expr: Variable: 62
                         └──Type expr: Variable: 63
                   └──Constraint:
                      └──Type expr: Variable: 61
                      └──Type expr: Variable: 62
                   └──Constraint:
                      └──Type expr: Variable: 63
                      └──Type expr: Constructor: bool
                └──Constructor declaration:
                   └──Constructor name: Leq
                   └──Constructor alphas: 61 62 63
                   └──Constructor type:
                      └──Type expr: Constructor: bin_op
                         └──Type expr: Variable: 61
                         └──Type expr: Variable: 62
                         └──Type expr: Variable: 63
                   └──Constraint:
                      └──Type expr: Variable: 61
                      └──Type expr: Variable: 62
                   └──Constraint:
                      └──Type expr: Variable: 63
                      └──Type expr: Constructor: bool
                └──Constructor declaration:
                   └──Constructor name: Add
                   └──Constructor alphas: 61 62 63
                   └──Constructor type:
                      └──Type expr: Constructor: bin_op
                         └──Type expr: Variable: 61
                         └──Type expr: Variable: 62
                         └──Type expr: Variable: 63
                   └──Constraint:
                      └──Type expr: Variable: 61
                      └──Type expr: Constructor: int
                   └──Constraint:
                      └──Type expr: Variable: 62
                      └──Type expr: Constructor: int
                   └──Constraint:
                      └──Type expr: Variable: 63
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
                         └──Type expr: Variable: 41
                         └──Type expr: Variable: 42
                         └──Type expr: Variable: 43
                      └──Type expr: Arrow
                         └──Type expr: Constructor: constant
                            └──Type expr: Variable: 41
                         └──Type expr: Arrow
                            └──Type expr: Constructor: constant
                               └──Type expr: Variable: 42
                            └──Type expr: Constructor: constant
                               └──Type expr: Variable: 43
                   └──Desc: Variable: eval
                └──Abstraction:
                   └──Variables: 41,42,43
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: bin_op
                            └──Type expr: Variable: 41
                            └──Type expr: Variable: 42
                            └──Type expr: Variable: 43
                         └──Type expr: Arrow
                            └──Type expr: Constructor: constant
                               └──Type expr: Variable: 41
                            └──Type expr: Arrow
                               └──Type expr: Constructor: constant
                                  └──Type expr: Variable: 42
                               └──Type expr: Constructor: constant
                                  └──Type expr: Variable: 43
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: bin_op
                               └──Type expr: Variable: 41
                               └──Type expr: Variable: 42
                               └──Type expr: Variable: 43
                            └──Desc: Variable: bop
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: constant
                                  └──Type expr: Variable: 41
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: constant
                                     └──Type expr: Variable: 42
                                  └──Type expr: Constructor: constant
                                     └──Type expr: Variable: 43
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: constant
                                     └──Type expr: Variable: 41
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: constant
                                        └──Type expr: Variable: 42
                                     └──Type expr: Constructor: constant
                                        └──Type expr: Variable: 43
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: constant
                                           └──Type expr: Variable: 42
                                        └──Desc: Variable: y
                                     └──Expression:
                                        └──Type expr: Constructor: constant
                                           └──Type expr: Variable: 43
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: bin_op
                                                    └──Type expr: Variable: 41
                                                    └──Type expr: Variable: 42
                                                    └──Type expr: Variable: 43
                                                 └──Type expr: Constructor: constant
                                                    └──Type expr: Variable: 41
                                                 └──Type expr: Constructor: constant
                                                    └──Type expr: Variable: 42
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: bin_op
                                                       └──Type expr: Variable: 41
                                                       └──Type expr: Variable: 42
                                                       └──Type expr: Variable: 43
                                                    └──Desc: Variable
                                                       └──Variable: bop
                                                 └──Expression:
                                                    └──Type expr: Constructor: constant
                                                       └──Type expr: Variable: 41
                                                    └──Desc: Variable
                                                       └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: constant
                                                       └──Type expr: Variable: 42
                                                    └──Desc: Variable
                                                       └──Variable: y
                                           └──Type expr: Tuple
                                              └──Type expr: Constructor: bin_op
                                                 └──Type expr: Variable: 41
                                                 └──Type expr: Variable: 42
                                                 └──Type expr: Variable: 43
                                              └──Type expr: Constructor: constant
                                                 └──Type expr: Variable: 41
                                              └──Type expr: Constructor: constant
                                                 └──Type expr: Variable: 42
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: bin_op
                                                          └──Type expr: Variable: 41
                                                          └──Type expr: Variable: 42
                                                          └──Type expr: Variable: 43
                                                       └──Type expr: Constructor: constant
                                                          └──Type expr: Variable: 41
                                                       └──Type expr: Constructor: constant
                                                          └──Type expr: Variable: 42
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: bin_op
                                                             └──Type expr: Variable: 41
                                                             └──Type expr: Variable: 42
                                                             └──Type expr: Variable: 43
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Eq
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: bin_op
                                                                      └──Type expr: Variable: 41
                                                                      └──Type expr: Variable: 42
                                                                      └──Type expr: Variable: 43
                                                       └──Pattern:
                                                          └──Type expr: Constructor: constant
                                                             └──Type expr: Variable: 41
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Bool
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: bool
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: constant
                                                                      └──Type expr: Variable: 41
                                                             └──Pattern:
                                                                └──Type expr: Constructor: bool
                                                                └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: constant
                                                             └──Type expr: Variable: 42
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Bool
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: bool
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: constant
                                                                      └──Type expr: Variable: 42
                                                             └──Pattern:
                                                                └──Type expr: Constructor: bool
                                                                └──Desc: Variable: y
                                                 └──Expression:
                                                    └──Type expr: Constructor: constant
                                                       └──Type expr: Variable: 43
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Bool
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: bool
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: constant
                                                                └──Type expr: Variable: 43
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
                                                          └──Type expr: Variable: 41
                                                          └──Type expr: Variable: 42
                                                          └──Type expr: Variable: 43
                                                       └──Type expr: Constructor: constant
                                                          └──Type expr: Variable: 41
                                                       └──Type expr: Constructor: constant
                                                          └──Type expr: Variable: 42
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: bin_op
                                                             └──Type expr: Variable: 41
                                                             └──Type expr: Variable: 42
                                                             └──Type expr: Variable: 43
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Eq
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: bin_op
                                                                      └──Type expr: Variable: 41
                                                                      └──Type expr: Variable: 42
                                                                      └──Type expr: Variable: 43
                                                       └──Pattern:
                                                          └──Type expr: Constructor: constant
                                                             └──Type expr: Variable: 41
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Int
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: int
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: constant
                                                                      └──Type expr: Variable: 41
                                                             └──Pattern:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: constant
                                                             └──Type expr: Variable: 42
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Int
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: int
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: constant
                                                                      └──Type expr: Variable: 42
                                                             └──Pattern:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable: y
                                                 └──Expression:
                                                    └──Type expr: Constructor: constant
                                                       └──Type expr: Variable: 43
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Bool
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: bool
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: constant
                                                                └──Type expr: Variable: 43
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
                                                          └──Type expr: Variable: 41
                                                          └──Type expr: Variable: 42
                                                          └──Type expr: Variable: 43
                                                       └──Type expr: Constructor: constant
                                                          └──Type expr: Variable: 41
                                                       └──Type expr: Constructor: constant
                                                          └──Type expr: Variable: 42
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: bin_op
                                                             └──Type expr: Variable: 41
                                                             └──Type expr: Variable: 42
                                                             └──Type expr: Variable: 43
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Leq
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: bin_op
                                                                      └──Type expr: Variable: 41
                                                                      └──Type expr: Variable: 42
                                                                      └──Type expr: Variable: 43
                                                       └──Pattern:
                                                          └──Type expr: Constructor: constant
                                                             └──Type expr: Variable: 41
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Int
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: int
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: constant
                                                                      └──Type expr: Variable: 41
                                                             └──Pattern:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: constant
                                                             └──Type expr: Variable: 42
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Int
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: int
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: constant
                                                                      └──Type expr: Variable: 42
                                                             └──Pattern:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable: y
                                                 └──Expression:
                                                    └──Type expr: Constructor: constant
                                                       └──Type expr: Variable: 43
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Bool
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: bool
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: constant
                                                                └──Type expr: Variable: 43
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
                                                          └──Type expr: Variable: 41
                                                          └──Type expr: Variable: 42
                                                          └──Type expr: Variable: 43
                                                       └──Type expr: Constructor: constant
                                                          └──Type expr: Variable: 41
                                                       └──Type expr: Constructor: constant
                                                          └──Type expr: Variable: 42
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: bin_op
                                                             └──Type expr: Variable: 41
                                                             └──Type expr: Variable: 42
                                                             └──Type expr: Variable: 43
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Leq
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: bin_op
                                                                      └──Type expr: Variable: 41
                                                                      └──Type expr: Variable: 42
                                                                      └──Type expr: Variable: 43
                                                       └──Pattern:
                                                          └──Type expr: Constructor: constant
                                                             └──Type expr: Variable: 41
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Bool
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: bool
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: constant
                                                                      └──Type expr: Variable: 41
                                                             └──Pattern:
                                                                └──Type expr: Constructor: bool
                                                                └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: constant
                                                             └──Type expr: Variable: 42
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Bool
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: bool
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: constant
                                                                      └──Type expr: Variable: 42
                                                             └──Pattern:
                                                                └──Type expr: Constructor: bool
                                                                └──Desc: Variable: y
                                                 └──Expression:
                                                    └──Type expr: Constructor: constant
                                                       └──Type expr: Variable: 43
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Bool
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: bool
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: constant
                                                                └──Type expr: Variable: 43
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
                                                          └──Type expr: Variable: 41
                                                          └──Type expr: Variable: 42
                                                          └──Type expr: Variable: 43
                                                       └──Type expr: Constructor: constant
                                                          └──Type expr: Variable: 41
                                                       └──Type expr: Constructor: constant
                                                          └──Type expr: Variable: 42
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: bin_op
                                                             └──Type expr: Variable: 41
                                                             └──Type expr: Variable: 42
                                                             └──Type expr: Variable: 43
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Add
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: bin_op
                                                                      └──Type expr: Variable: 41
                                                                      └──Type expr: Variable: 42
                                                                      └──Type expr: Variable: 43
                                                       └──Pattern:
                                                          └──Type expr: Constructor: constant
                                                             └──Type expr: Variable: 41
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Int
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: int
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: constant
                                                                      └──Type expr: Variable: 41
                                                             └──Pattern:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: constant
                                                             └──Type expr: Variable: 42
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Int
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: int
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: constant
                                                                      └──Type expr: Variable: 42
                                                             └──Pattern:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable: y
                                                 └──Expression:
                                                    └──Type expr: Constructor: constant
                                                       └──Type expr: Variable: 43
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Int
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: constant
                                                                └──Type expr: Variable: 43
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
