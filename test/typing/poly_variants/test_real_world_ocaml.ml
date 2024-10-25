open! Import
open Util

(* Examples taken from https://dev.realworldocaml.org/variants.html *)

let%expect_test "" =
  let str =
    {|
      let three = `Int 3;;

      let four = `Float 4.0;;

      let nan = `Not_a_number;;

      type 'a list = 
        | Nil 
        | Cons of 'a * 'a list
      ;;

      let _ = 
        Cons (three, Cons (four, Cons (nan, Nil)))
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Variant
                      └──Type expr: Row cons
                         └──Label: Int
                         └──Type expr: Constructor: present
                            └──Type expr: Constructor: int
                         └──Type expr: Variable: 2
                   └──Desc: Variable: three
                └──Abstraction:
                   └──Variables: 2
                   └──Expression:
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Int
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: int
                            └──Type expr: Variable: 2
                      └──Desc: Variant
                         └──Variant description:
                            └──Tag: Int
                            └──Variant row:
                               └──Type expr: Row cons
                                  └──Label: Int
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: int
                                  └──Type expr: Variable: 2
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Constant: 3
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Variant
                      └──Type expr: Row cons
                         └──Label: Float
                         └──Type expr: Constructor: present
                            └──Type expr: Constructor: float
                         └──Type expr: Variable: 14
                   └──Desc: Variable: four
                └──Abstraction:
                   └──Variables: 14
                   └──Expression:
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Float
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: float
                            └──Type expr: Variable: 14
                      └──Desc: Variant
                         └──Variant description:
                            └──Tag: Float
                            └──Variant row:
                               └──Type expr: Row cons
                                  └──Label: Float
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: float
                                  └──Type expr: Variable: 14
                         └──Expression:
                            └──Type expr: Constructor: float
                            └──Desc: Constant: 4.000000
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Variant
                      └──Type expr: Row cons
                         └──Label: Not_a_number
                         └──Type expr: Constructor: present
                            └──Type expr: Constructor: unit
                         └──Type expr: Variable: 26
                   └──Desc: Variable: nan
                └──Abstraction:
                   └──Variables: 26
                   └──Expression:
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Not_a_number
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: unit
                            └──Type expr: Variable: 26
                      └──Desc: Variant
                         └──Variant description:
                            └──Tag: Not_a_number
                            └──Variant row:
                               └──Type expr: Row cons
                                  └──Label: Not_a_number
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Variable: 26
       └──Structure item: Type
          └──Type declaration:
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: 591
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 591
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 591
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 591
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: 591
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 591
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: list
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Float
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: float
                            └──Type expr: Row cons
                               └──Label: Int
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: int
                               └──Type expr: Row cons
                                  └──Label: Not_a_number
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Variable: 90
                   └──Desc: Any
                └──Abstraction:
                   └──Variables: 90
                   └──Expression:
                      └──Type expr: Constructor: list
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Float
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: float
                               └──Type expr: Row cons
                                  └──Label: Int
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: int
                                  └──Type expr: Row cons
                                     └──Label: Not_a_number
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Variable: 90
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Cons
                            └──Constructor argument type:
                               └──Type expr: Tuple
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Float
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: float
                                        └──Type expr: Row cons
                                           └──Label: Int
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: int
                                           └──Type expr: Row cons
                                              └──Label: Not_a_number
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: 90
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Float
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: float
                                           └──Type expr: Row cons
                                              └──Label: Int
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Row cons
                                                 └──Label: Not_a_number
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Variable: 90
                            └──Constructor type:
                               └──Type expr: Constructor: list
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Float
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: float
                                        └──Type expr: Row cons
                                           └──Label: Int
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: int
                                           └──Type expr: Row cons
                                              └──Label: Not_a_number
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: 90
                         └──Expression:
                            └──Type expr: Tuple
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Float
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: float
                                     └──Type expr: Row cons
                                        └──Label: Int
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: int
                                        └──Type expr: Row cons
                                           └──Label: Not_a_number
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: 90
                               └──Type expr: Constructor: list
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Float
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: float
                                        └──Type expr: Row cons
                                           └──Label: Int
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: int
                                           └──Type expr: Row cons
                                              └──Label: Not_a_number
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: 90
                            └──Desc: Tuple
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Float
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: float
                                        └──Type expr: Row cons
                                           └──Label: Int
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: int
                                           └──Type expr: Row cons
                                              └──Label: Not_a_number
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: 90
                                  └──Desc: Variable
                                     └──Variable: three
                                     └──Type expr: Row cons
                                        └──Label: Float
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: float
                                        └──Type expr: Row cons
                                           └──Label: Not_a_number
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: 90
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Float
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: float
                                           └──Type expr: Row cons
                                              └──Label: Int
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Row cons
                                                 └──Label: Not_a_number
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Variable: 90
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Cons
                                        └──Constructor argument type:
                                           └──Type expr: Tuple
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Float
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: float
                                                    └──Type expr: Row cons
                                                       └──Label: Int
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: int
                                                       └──Type expr: Row cons
                                                          └──Label: Not_a_number
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: 90
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Float
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: float
                                                       └──Type expr: Row cons
                                                          └──Label: Int
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Row cons
                                                             └──Label: Not_a_number
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: 90
                                        └──Constructor type:
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Float
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: float
                                                    └──Type expr: Row cons
                                                       └──Label: Int
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: int
                                                       └──Type expr: Row cons
                                                          └──Label: Not_a_number
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: 90
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Float
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: float
                                                 └──Type expr: Row cons
                                                    └──Label: Int
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row cons
                                                       └──Label: Not_a_number
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: 90
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Float
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: float
                                                    └──Type expr: Row cons
                                                       └──Label: Int
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: int
                                                       └──Type expr: Row cons
                                                          └──Label: Not_a_number
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: 90
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Float
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: float
                                                    └──Type expr: Row cons
                                                       └──Label: Int
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: int
                                                       └──Type expr: Row cons
                                                          └──Label: Not_a_number
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: 90
                                              └──Desc: Variable
                                                 └──Variable: four
                                                 └──Type expr: Row cons
                                                    └──Label: Int
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row cons
                                                       └──Label: Not_a_number
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: 90
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Float
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: float
                                                       └──Type expr: Row cons
                                                          └──Label: Int
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Row cons
                                                             └──Label: Not_a_number
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: 90
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Float
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: float
                                                                └──Type expr: Row cons
                                                                   └──Label: Int
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: int
                                                                   └──Type expr: Row cons
                                                                      └──Label: Not_a_number
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: 90
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Float
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: float
                                                                   └──Type expr: Row cons
                                                                      └──Label: Int
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: int
                                                                      └──Type expr: Row cons
                                                                         └──Label: Not_a_number
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 90
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Float
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: float
                                                                └──Type expr: Row cons
                                                                   └──Label: Int
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: int
                                                                   └──Type expr: Row cons
                                                                      └──Label: Not_a_number
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: 90
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Float
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: float
                                                             └──Type expr: Row cons
                                                                └──Label: Int
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: int
                                                                └──Type expr: Row cons
                                                                   └──Label: Not_a_number
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: 90
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Float
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: float
                                                                └──Type expr: Row cons
                                                                   └──Label: Int
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: int
                                                                   └──Type expr: Row cons
                                                                      └──Label: Not_a_number
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: 90
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Float
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: float
                                                                └──Type expr: Row cons
                                                                   └──Label: Int
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: int
                                                                   └──Type expr: Row cons
                                                                      └──Label: Not_a_number
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: 90
                                                          └──Desc: Variable
                                                             └──Variable: nan
                                                             └──Type expr: Row cons
                                                                └──Label: Float
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: float
                                                                └──Type expr: Row cons
                                                                   └──Label: Int
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: int
                                                                   └──Type expr: Variable: 90
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Float
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: float
                                                                   └──Type expr: Row cons
                                                                      └──Label: Int
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: int
                                                                      └──Type expr: Row cons
                                                                         └──Label: Not_a_number
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 90
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Nil
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Float
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: float
                                                                            └──Type expr: Row cons
                                                                               └──Label: Int
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: int
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Not_a_number
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: 90 |}]


let%expect_test "" =
  let str =
    {|
      type 'a list = 
        | Nil 
        | Cons of 'a * 'a list
      ;;

      let three = `Int 3;;
      let four = `Float 4.0;;
      let five = `Int "five";;

      let _ = 
        Cons (three, Cons (four, Cons (five, Nil)))
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    ("Cannot unify types"
     ("Type_expr.decode type_expr1"
      (Type 72
       (Former
        (Variant
         (Type 49
          (Row_cons Float
           (Type 67
            (Former (Constr ((Type 68 (Former (Constr () float)))) present)))
           (Type 66
            (Row_cons Int
             (Type 51
              (Former (Constr ((Type 52 (Former (Constr () int)))) present)))
             (Type 69 (Var 69))))))))))
     ("Type_expr.decode type_expr2"
      (Type 83
       (Former
        (Variant
         (Type 84
          (Row_cons Int
           (Type 86
            (Former (Constr ((Type 87 (Former (Constr () string)))) present)))
           (Type 85 (Var 85))))))))) |}]


let%expect_test "" =
  let str =
    {|
      external gt : 'a. 'a -> 'a -> bool = "%greater_than";;

      let is_positive = 
        fun t ->
          match t with
          ( `Int x -> gt x 0
          | `Float x -> gt x 0.0 
          )
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Primitive
          └──Value description:
             └──Name: gt
             └──Scheme:
                └──Variables: 0
                └──Type expr: Arrow
                   └──Type expr: Variable: 0
                   └──Type expr: Arrow
                      └──Type expr: Variable: 0
                      └──Type expr: Constructor: bool
             └──Primitive name: %greater_than
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Int
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: int
                            └──Type expr: Row cons
                               └──Label: Float
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: float
                               └──Type expr: Row uniform
                                  └──Type expr: Constructor: absent
                      └──Type expr: Constructor: bool
                   └──Desc: Variable: is_positive
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Int
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: int
                               └──Type expr: Row cons
                                  └──Label: Float
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: float
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Int
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: int
                                  └──Type expr: Row cons
                                     └──Label: Float
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: float
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: bool
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Int
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: int
                                        └──Type expr: Row cons
                                           └──Label: Float
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: float
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Int
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: int
                                     └──Type expr: Row cons
                                        └──Label: Float
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: float
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Int
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Row cons
                                                 └──Label: Float
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: float
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Int
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Int
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row cons
                                                       └──Label: Float
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: float
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                           └──Pattern:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable: x
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
                                                       └──Variable: gt
                                                       └──Type expr: Constructor: int
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 0
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Int
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Row cons
                                                 └──Label: Float
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: float
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Float
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Int
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row cons
                                                       └──Label: Float
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: float
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                           └──Pattern:
                                              └──Type expr: Constructor: float
                                              └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: bool
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: float
                                                 └──Type expr: Constructor: bool
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: float
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: float
                                                          └──Type expr: Constructor: bool
                                                    └──Desc: Variable
                                                       └──Variable: gt
                                                       └──Type expr: Constructor: float
                                                 └──Expression:
                                                    └──Type expr: Constructor: float
                                                    └──Desc: Variable
                                                       └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: float
                                              └──Desc: Constant: 0.000000 |}]


let%expect_test "" =
  let str =
    {|
      type 'a list = 
        | Nil 
        | Cons of 'a * 'a list
      ;;

      external gt : 'a. 'a -> 'a -> bool = "%greater_than";;

      let is_positive = 
        fun t ->
          match t with
          ( `Int x -> gt x 0
          | `Float x -> gt x 0.0 
          )
      ;;

      external filter : 'a. 'a list -> ('a -> bool) -> 'a list = "%filter";;

      let exact = 
        filter (Cons (`Int 3, Cons (`Float 4.0, Nil))) is_positive
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
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: 67
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 67
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 67
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 67
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: 67
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 67
       └──Structure item: Primitive
          └──Value description:
             └──Name: gt
             └──Scheme:
                └──Variables: 0
                └──Type expr: Arrow
                   └──Type expr: Variable: 0
                   └──Type expr: Arrow
                      └──Type expr: Variable: 0
                      └──Type expr: Constructor: bool
             └──Primitive name: %greater_than
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Int
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: int
                            └──Type expr: Row cons
                               └──Label: Float
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: float
                               └──Type expr: Row uniform
                                  └──Type expr: Constructor: absent
                      └──Type expr: Constructor: bool
                   └──Desc: Variable: is_positive
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Int
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: int
                               └──Type expr: Row cons
                                  └──Label: Float
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: float
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Int
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: int
                                  └──Type expr: Row cons
                                     └──Label: Float
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: float
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: bool
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Int
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: int
                                        └──Type expr: Row cons
                                           └──Label: Float
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: float
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Int
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: int
                                     └──Type expr: Row cons
                                        └──Label: Float
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: float
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Int
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Row cons
                                                 └──Label: Float
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: float
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Int
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Int
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row cons
                                                       └──Label: Float
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: float
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                           └──Pattern:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable: x
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
                                                       └──Variable: gt
                                                       └──Type expr: Constructor: int
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 0
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Int
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Row cons
                                                 └──Label: Float
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: float
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Float
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Int
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row cons
                                                       └──Label: Float
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: float
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                           └──Pattern:
                                              └──Type expr: Constructor: float
                                              └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: bool
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: float
                                                 └──Type expr: Constructor: bool
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: float
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: float
                                                          └──Type expr: Constructor: bool
                                                    └──Desc: Variable
                                                       └──Variable: gt
                                                       └──Type expr: Constructor: float
                                                 └──Expression:
                                                    └──Type expr: Constructor: float
                                                    └──Desc: Variable
                                                       └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: float
                                              └──Desc: Constant: 0.000000
       └──Structure item: Primitive
          └──Value description:
             └──Name: filter
             └──Scheme:
                └──Variables: 67
                └──Type expr: Arrow
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: 67
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: 67
                         └──Type expr: Constructor: bool
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 67
             └──Primitive name: %filter
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: list
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Float
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: float
                            └──Type expr: Row cons
                               └──Label: Int
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: int
                               └──Type expr: Row uniform
                                  └──Type expr: Constructor: absent
                   └──Desc: Variable: exact
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: list
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Float
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: float
                               └──Type expr: Row cons
                                  └──Label: Int
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: int
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                      └──Desc: Application
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Float
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: float
                                        └──Type expr: Row cons
                                           └──Label: Int
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: int
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                                  └──Type expr: Constructor: bool
                               └──Type expr: Constructor: list
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Float
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: float
                                        └──Type expr: Row cons
                                           └──Label: Int
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: int
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Float
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: float
                                              └──Type expr: Row cons
                                                 └──Label: Int
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                     └──Type expr: Arrow
                                        └──Type expr: Arrow
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Float
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: float
                                                 └──Type expr: Row cons
                                                    └──Label: Int
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                           └──Type expr: Constructor: bool
                                        └──Type expr: Constructor: list
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Float
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: float
                                                 └──Type expr: Row cons
                                                    └──Label: Int
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                  └──Desc: Variable
                                     └──Variable: filter
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Float
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: float
                                           └──Type expr: Row cons
                                              └──Label: Int
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Float
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: float
                                           └──Type expr: Row cons
                                              └──Label: Int
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Cons
                                        └──Constructor argument type:
                                           └──Type expr: Tuple
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Float
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: float
                                                    └──Type expr: Row cons
                                                       └──Label: Int
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: int
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Float
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: float
                                                       └──Type expr: Row cons
                                                          └──Label: Int
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                        └──Constructor type:
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Float
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: float
                                                    └──Type expr: Row cons
                                                       └──Label: Int
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: int
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Float
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: float
                                                 └──Type expr: Row cons
                                                    └──Label: Int
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Float
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: float
                                                    └──Type expr: Row cons
                                                       └──Label: Int
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: int
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Float
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: float
                                                    └──Type expr: Row cons
                                                       └──Label: Int
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: int
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                              └──Desc: Variant
                                                 └──Variant description:
                                                    └──Tag: Int
                                                    └──Variant row:
                                                       └──Type expr: Row cons
                                                          └──Label: Float
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: float
                                                          └──Type expr: Row cons
                                                             └──Label: Int
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: int
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 3
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Float
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: float
                                                       └──Type expr: Row cons
                                                          └──Label: Int
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Float
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: float
                                                                └──Type expr: Row cons
                                                                   └──Label: Int
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: int
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Float
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: float
                                                                   └──Type expr: Row cons
                                                                      └──Label: Int
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: int
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Float
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: float
                                                                └──Type expr: Row cons
                                                                   └──Label: Int
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: int
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Float
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: float
                                                             └──Type expr: Row cons
                                                                └──Label: Int
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: int
                                                                └──Type expr: Row uniform
                                                                   └──Type expr: Constructor: absent
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Float
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: float
                                                                └──Type expr: Row cons
                                                                   └──Label: Int
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: int
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Float
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: float
                                                                └──Type expr: Row cons
                                                                   └──Label: Int
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: int
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                          └──Desc: Variant
                                                             └──Variant description:
                                                                └──Tag: Float
                                                                └──Variant row:
                                                                   └──Type expr: Row cons
                                                                      └──Label: Float
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: float
                                                                      └──Type expr: Row cons
                                                                         └──Label: Int
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: int
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                                             └──Expression:
                                                                └──Type expr: Constructor: float
                                                                └──Desc: Constant: 4.000000
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Float
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: float
                                                                   └──Type expr: Row cons
                                                                      └──Label: Int
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: int
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Nil
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Float
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: float
                                                                            └──Type expr: Row cons
                                                                               └──Label: Int
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: int
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Float
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: float
                                     └──Type expr: Row cons
                                        └──Label: Int
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: int
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                               └──Type expr: Constructor: bool
                            └──Desc: Variable
                               └──Variable: is_positive |}]


let%expect_test "" =
  let str =
    {|
      type 'a list = 
        | Nil 
        | Cons of 'a * 'a list
      ;;

      external gt : 'a. 'a -> 'a -> bool = "%greater_than";;

      type ('a, 'err) result = 
        | Ok of 'a
        | Error of 'err
      ;;

      let is_positive = 
        fun t ->
          match t with
          ( `Int x -> Ok (gt x 0)
          | `Float x -> Ok (gt x 0.0)
          | `Not_a_number -> Error "not a number" 
          )
      ;;

      external filter : 'a. 'a list -> ('a -> bool) -> 'a list = "%filter";;

      let _ = 
        filter (Cons (`Int 3, Cons (`Float 4.0, Nil))) (fun x ->
          match is_positive x with
          ( Error _ -> false 
          | Ok b -> b
          ))
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
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: 158
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 158
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 158
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 158
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: 158
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 158
       └──Structure item: Primitive
          └──Value description:
             └──Name: gt
             └──Scheme:
                └──Variables: 0
                └──Type expr: Arrow
                   └──Type expr: Variable: 0
                   └──Type expr: Arrow
                      └──Type expr: Variable: 0
                      └──Type expr: Constructor: bool
             └──Primitive name: %greater_than
       └──Structure item: Type
          └──Type declaration:
             └──Type name: result
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Ok
                   └──Constructor alphas: 163 164
                   └──Constructor type:
                      └──Type expr: Constructor: result
                         └──Type expr: Variable: 163
                         └──Type expr: Variable: 164
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: 163
                └──Constructor declaration:
                   └──Constructor name: Error
                   └──Constructor alphas: 163 164
                   └──Constructor type:
                      └──Type expr: Constructor: result
                         └──Type expr: Variable: 163
                         └──Type expr: Variable: 164
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: 164
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Int
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: int
                            └──Type expr: Row cons
                               └──Label: Float
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: float
                               └──Type expr: Row cons
                                  └──Label: Not_a_number
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                      └──Type expr: Constructor: result
                         └──Type expr: Constructor: bool
                         └──Type expr: Constructor: string
                   └──Desc: Variable: is_positive
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Int
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: int
                               └──Type expr: Row cons
                                  └──Label: Float
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: float
                                  └──Type expr: Row cons
                                     └──Label: Not_a_number
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Constructor: result
                            └──Type expr: Constructor: bool
                            └──Type expr: Constructor: string
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Int
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: int
                                  └──Type expr: Row cons
                                     └──Label: Float
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: float
                                     └──Type expr: Row cons
                                        └──Label: Not_a_number
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: result
                               └──Type expr: Constructor: bool
                               └──Type expr: Constructor: string
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Int
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: int
                                        └──Type expr: Row cons
                                           └──Label: Float
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: float
                                           └──Type expr: Row cons
                                              └──Label: Not_a_number
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Int
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: int
                                     └──Type expr: Row cons
                                        └──Label: Float
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: float
                                        └──Type expr: Row cons
                                           └──Label: Not_a_number
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Int
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Row cons
                                                 └──Label: Float
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: float
                                                 └──Type expr: Row cons
                                                    └──Label: Not_a_number
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Int
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Int
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row cons
                                                       └──Label: Float
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: float
                                                       └──Type expr: Row cons
                                                          └──Label: Not_a_number
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                           └──Pattern:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: result
                                           └──Type expr: Constructor: bool
                                           └──Type expr: Constructor: string
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Ok
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: bool
                                              └──Constructor type:
                                                 └──Type expr: Constructor: result
                                                    └──Type expr: Constructor: bool
                                                    └──Type expr: Constructor: string
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
                                                             └──Variable: gt
                                                             └──Type expr: Constructor: int
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 0
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Int
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Row cons
                                                 └──Label: Float
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: float
                                                 └──Type expr: Row cons
                                                    └──Label: Not_a_number
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Float
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Int
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row cons
                                                       └──Label: Float
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: float
                                                       └──Type expr: Row cons
                                                          └──Label: Not_a_number
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                           └──Pattern:
                                              └──Type expr: Constructor: float
                                              └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: result
                                           └──Type expr: Constructor: bool
                                           └──Type expr: Constructor: string
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Ok
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: bool
                                              └──Constructor type:
                                                 └──Type expr: Constructor: result
                                                    └──Type expr: Constructor: bool
                                                    └──Type expr: Constructor: string
                                           └──Expression:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: float
                                                       └──Type expr: Constructor: bool
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: float
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: float
                                                                └──Type expr: Constructor: bool
                                                          └──Desc: Variable
                                                             └──Variable: gt
                                                             └──Type expr: Constructor: float
                                                       └──Expression:
                                                          └──Type expr: Constructor: float
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: float
                                                    └──Desc: Constant: 0.000000
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Int
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Row cons
                                                 └──Label: Float
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: float
                                                 └──Type expr: Row cons
                                                    └──Label: Not_a_number
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Not_a_number
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Int
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row cons
                                                       └──Label: Float
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: float
                                                       └──Type expr: Row cons
                                                          └──Label: Not_a_number
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                     └──Expression:
                                        └──Type expr: Constructor: result
                                           └──Type expr: Constructor: bool
                                           └──Type expr: Constructor: string
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Error
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: string
                                              └──Constructor type:
                                                 └──Type expr: Constructor: result
                                                    └──Type expr: Constructor: bool
                                                    └──Type expr: Constructor: string
                                           └──Expression:
                                              └──Type expr: Constructor: string
                                              └──Desc: Constant: not a number
       └──Structure item: Primitive
          └──Value description:
             └──Name: filter
             └──Scheme:
                └──Variables: 94
                └──Type expr: Arrow
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: 94
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: 94
                         └──Type expr: Constructor: bool
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 94
             └──Primitive name: %filter
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: list
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Float
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: float
                            └──Type expr: Row cons
                               └──Label: Int
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: int
                               └──Type expr: Row cons
                                  └──Label: Not_a_number
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                   └──Desc: Any
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: list
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Float
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: float
                               └──Type expr: Row cons
                                  └──Label: Int
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: int
                                  └──Type expr: Row cons
                                     └──Label: Not_a_number
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                      └──Desc: Application
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Float
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: float
                                        └──Type expr: Row cons
                                           └──Label: Int
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: int
                                           └──Type expr: Row cons
                                              └──Label: Not_a_number
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                                  └──Type expr: Constructor: bool
                               └──Type expr: Constructor: list
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Float
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: float
                                        └──Type expr: Row cons
                                           └──Label: Int
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: int
                                           └──Type expr: Row cons
                                              └──Label: Not_a_number
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Float
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: float
                                              └──Type expr: Row cons
                                                 └──Label: Int
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Row cons
                                                    └──Label: Not_a_number
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                     └──Type expr: Arrow
                                        └──Type expr: Arrow
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Float
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: float
                                                 └──Type expr: Row cons
                                                    └──Label: Int
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row cons
                                                       └──Label: Not_a_number
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                           └──Type expr: Constructor: bool
                                        └──Type expr: Constructor: list
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Float
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: float
                                                 └──Type expr: Row cons
                                                    └──Label: Int
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row cons
                                                       └──Label: Not_a_number
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                  └──Desc: Variable
                                     └──Variable: filter
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Float
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: float
                                           └──Type expr: Row cons
                                              └──Label: Int
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Row cons
                                                 └──Label: Not_a_number
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Float
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: float
                                           └──Type expr: Row cons
                                              └──Label: Int
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Row cons
                                                 └──Label: Not_a_number
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Cons
                                        └──Constructor argument type:
                                           └──Type expr: Tuple
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Float
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: float
                                                    └──Type expr: Row cons
                                                       └──Label: Int
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: int
                                                       └──Type expr: Row cons
                                                          └──Label: Not_a_number
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Float
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: float
                                                       └──Type expr: Row cons
                                                          └──Label: Int
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Row cons
                                                             └──Label: Not_a_number
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                        └──Constructor type:
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Float
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: float
                                                    └──Type expr: Row cons
                                                       └──Label: Int
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: int
                                                       └──Type expr: Row cons
                                                          └──Label: Not_a_number
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Float
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: float
                                                 └──Type expr: Row cons
                                                    └──Label: Int
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row cons
                                                       └──Label: Not_a_number
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Float
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: float
                                                    └──Type expr: Row cons
                                                       └──Label: Int
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: int
                                                       └──Type expr: Row cons
                                                          └──Label: Not_a_number
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Float
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: float
                                                    └──Type expr: Row cons
                                                       └──Label: Int
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: int
                                                       └──Type expr: Row cons
                                                          └──Label: Not_a_number
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                              └──Desc: Variant
                                                 └──Variant description:
                                                    └──Tag: Int
                                                    └──Variant row:
                                                       └──Type expr: Row cons
                                                          └──Label: Float
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: float
                                                          └──Type expr: Row cons
                                                             └──Label: Int
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: int
                                                             └──Type expr: Row cons
                                                                └──Label: Not_a_number
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row uniform
                                                                   └──Type expr: Constructor: absent
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 3
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Float
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: float
                                                       └──Type expr: Row cons
                                                          └──Label: Int
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Row cons
                                                             └──Label: Not_a_number
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Float
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: float
                                                                └──Type expr: Row cons
                                                                   └──Label: Int
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: int
                                                                   └──Type expr: Row cons
                                                                      └──Label: Not_a_number
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Float
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: float
                                                                   └──Type expr: Row cons
                                                                      └──Label: Int
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: int
                                                                      └──Type expr: Row cons
                                                                         └──Label: Not_a_number
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Float
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: float
                                                                └──Type expr: Row cons
                                                                   └──Label: Int
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: int
                                                                   └──Type expr: Row cons
                                                                      └──Label: Not_a_number
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Float
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: float
                                                             └──Type expr: Row cons
                                                                └──Label: Int
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: int
                                                                └──Type expr: Row cons
                                                                   └──Label: Not_a_number
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Float
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: float
                                                                └──Type expr: Row cons
                                                                   └──Label: Int
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: int
                                                                   └──Type expr: Row cons
                                                                      └──Label: Not_a_number
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Float
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: float
                                                                └──Type expr: Row cons
                                                                   └──Label: Int
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: int
                                                                   └──Type expr: Row cons
                                                                      └──Label: Not_a_number
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                          └──Desc: Variant
                                                             └──Variant description:
                                                                └──Tag: Float
                                                                └──Variant row:
                                                                   └──Type expr: Row cons
                                                                      └──Label: Float
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: float
                                                                      └──Type expr: Row cons
                                                                         └──Label: Int
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: int
                                                                         └──Type expr: Row cons
                                                                            └──Label: Not_a_number
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row uniform
                                                                               └──Type expr: Constructor: absent
                                                             └──Expression:
                                                                └──Type expr: Constructor: float
                                                                └──Desc: Constant: 4.000000
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Float
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: float
                                                                   └──Type expr: Row cons
                                                                      └──Label: Int
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: int
                                                                      └──Type expr: Row cons
                                                                         └──Label: Not_a_number
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Nil
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Float
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: float
                                                                            └──Type expr: Row cons
                                                                               └──Label: Int
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: int
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Not_a_number
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row uniform
                                                                                     └──Type expr: Constructor: absent
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Float
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: float
                                     └──Type expr: Row cons
                                        └──Label: Int
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: int
                                        └──Type expr: Row cons
                                           └──Label: Not_a_number
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                               └──Type expr: Constructor: bool
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Float
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: float
                                        └──Type expr: Row cons
                                           └──Label: Int
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: int
                                           └──Type expr: Row cons
                                              └──Label: Not_a_number
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: result
                                           └──Type expr: Constructor: bool
                                           └──Type expr: Constructor: string
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Float
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: float
                                                       └──Type expr: Row cons
                                                          └──Label: Int
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Row cons
                                                             └──Label: Not_a_number
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                                 └──Type expr: Constructor: result
                                                    └──Type expr: Constructor: bool
                                                    └──Type expr: Constructor: string
                                              └──Desc: Variable
                                                 └──Variable: is_positive
                                           └──Expression:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Float
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: float
                                                    └──Type expr: Row cons
                                                       └──Label: Int
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: int
                                                       └──Type expr: Row cons
                                                          └──Label: Not_a_number
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                              └──Desc: Variable
                                                 └──Variable: x
                                     └──Type expr: Constructor: result
                                        └──Type expr: Constructor: bool
                                        └──Type expr: Constructor: string
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: result
                                                 └──Type expr: Constructor: bool
                                                 └──Type expr: Constructor: string
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Error
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: string
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: result
                                                          └──Type expr: Constructor: bool
                                                          └──Type expr: Constructor: string
                                                 └──Pattern:
                                                    └──Type expr: Constructor: string
                                                    └──Desc: Any
                                           └──Expression:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Constant: false
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: result
                                                 └──Type expr: Constructor: bool
                                                 └──Type expr: Constructor: string
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Ok
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: bool
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: result
                                                          └──Type expr: Constructor: bool
                                                          └──Type expr: Constructor: string
                                                 └──Pattern:
                                                    └──Type expr: Constructor: bool
                                                    └──Desc: Variable: b
                                           └──Expression:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Variable
                                                 └──Variable: b |}]


let%expect_test "" =
  let str =
    {|
      external gt : 'a. 'a -> 'a -> bool = "%greater_than";;

      type ('a, 'err) result = 
        | Ok of 'a
        | Error of 'err
      ;;

      let is_positive = 
        fun t ->
          match t with
          ( `Int x -> Ok (gt x 0)
          | `Float x -> Ok (gt x 0.0)
          | _ -> Error "unknown" 
          )
      ;;

      let _ = is_positive (`Int 0);;

      let _ = is_positive (`Rational (3, 4));;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Primitive
          └──Value description:
             └──Name: gt
             └──Scheme:
                └──Variables: 0
                └──Type expr: Arrow
                   └──Type expr: Variable: 0
                   └──Type expr: Arrow
                      └──Type expr: Variable: 0
                      └──Type expr: Constructor: bool
             └──Primitive name: %greater_than
       └──Structure item: Type
          └──Type declaration:
             └──Type name: result
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Ok
                   └──Constructor alphas: 208 209
                   └──Constructor type:
                      └──Type expr: Constructor: result
                         └──Type expr: Variable: 208
                         └──Type expr: Variable: 209
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: 208
                └──Constructor declaration:
                   └──Constructor name: Error
                   └──Constructor alphas: 208 209
                   └──Constructor type:
                      └──Type expr: Constructor: result
                         └──Type expr: Variable: 208
                         └──Type expr: Variable: 209
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: 209
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Int
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: int
                            └──Type expr: Row cons
                               └──Label: Float
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: float
                               └──Type expr: Variable: 14
                      └──Type expr: Constructor: result
                         └──Type expr: Constructor: bool
                         └──Type expr: Constructor: string
                   └──Desc: Variable: is_positive
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Int
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: int
                               └──Type expr: Row cons
                                  └──Label: Float
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: float
                                  └──Type expr: Variable: 14
                         └──Type expr: Constructor: result
                            └──Type expr: Constructor: bool
                            └──Type expr: Constructor: string
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Int
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: int
                                  └──Type expr: Row cons
                                     └──Label: Float
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: float
                                     └──Type expr: Variable: 14
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: result
                               └──Type expr: Constructor: bool
                               └──Type expr: Constructor: string
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Int
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: int
                                        └──Type expr: Row cons
                                           └──Label: Float
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: float
                                           └──Type expr: Variable: 14
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Int
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: int
                                     └──Type expr: Row cons
                                        └──Label: Float
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: float
                                        └──Type expr: Variable: 14
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Int
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Row cons
                                                 └──Label: Float
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: float
                                                 └──Type expr: Variable: 14
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Int
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Int
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row cons
                                                       └──Label: Float
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: float
                                                       └──Type expr: Variable: 14
                                           └──Pattern:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: result
                                           └──Type expr: Constructor: bool
                                           └──Type expr: Constructor: string
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Ok
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: bool
                                              └──Constructor type:
                                                 └──Type expr: Constructor: result
                                                    └──Type expr: Constructor: bool
                                                    └──Type expr: Constructor: string
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
                                                             └──Variable: gt
                                                             └──Type expr: Constructor: int
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 0
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Int
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Row cons
                                                 └──Label: Float
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: float
                                                 └──Type expr: Variable: 14
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Float
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Int
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row cons
                                                       └──Label: Float
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: float
                                                       └──Type expr: Variable: 14
                                           └──Pattern:
                                              └──Type expr: Constructor: float
                                              └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: result
                                           └──Type expr: Constructor: bool
                                           └──Type expr: Constructor: string
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Ok
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: bool
                                              └──Constructor type:
                                                 └──Type expr: Constructor: result
                                                    └──Type expr: Constructor: bool
                                                    └──Type expr: Constructor: string
                                           └──Expression:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: float
                                                       └──Type expr: Constructor: bool
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: float
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: float
                                                                └──Type expr: Constructor: bool
                                                          └──Desc: Variable
                                                             └──Variable: gt
                                                             └──Type expr: Constructor: float
                                                       └──Expression:
                                                          └──Type expr: Constructor: float
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: float
                                                    └──Desc: Constant: 0.000000
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Int
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Row cons
                                                 └──Label: Float
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: float
                                                 └──Type expr: Variable: 14
                                        └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Constructor: result
                                           └──Type expr: Constructor: bool
                                           └──Type expr: Constructor: string
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Error
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: string
                                              └──Constructor type:
                                                 └──Type expr: Constructor: result
                                                    └──Type expr: Constructor: bool
                                                    └──Type expr: Constructor: string
                                           └──Expression:
                                              └──Type expr: Constructor: string
                                              └──Desc: Constant: unknown
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: result
                      └──Type expr: Constructor: bool
                      └──Type expr: Constructor: string
                   └──Desc: Any
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: result
                         └──Type expr: Constructor: bool
                         └──Type expr: Constructor: string
                      └──Desc: Application
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Int
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: int
                                     └──Type expr: Row cons
                                        └──Label: Float
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: float
                                        └──Type expr: Variable: 85
                               └──Type expr: Constructor: result
                                  └──Type expr: Constructor: bool
                                  └──Type expr: Constructor: string
                            └──Desc: Variable
                               └──Variable: is_positive
                         └──Expression:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Int
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: int
                                  └──Type expr: Row cons
                                     └──Label: Float
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: float
                                     └──Type expr: Variable: 85
                            └──Desc: Variant
                               └──Variant description:
                                  └──Tag: Int
                                  └──Variant row:
                                     └──Type expr: Row cons
                                        └──Label: Int
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: int
                                        └──Type expr: Row cons
                                           └──Label: Float
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: float
                                           └──Type expr: Variable: 85
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Constant: 0
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: result
                      └──Type expr: Constructor: bool
                      └──Type expr: Constructor: string
                   └──Desc: Any
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: result
                         └──Type expr: Constructor: bool
                         └──Type expr: Constructor: string
                      └──Desc: Application
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Int
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: int
                                     └──Type expr: Row cons
                                        └──Label: Float
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: float
                                        └──Type expr: Row cons
                                           └──Label: Rational
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                           └──Type expr: Variable: 139
                               └──Type expr: Constructor: result
                                  └──Type expr: Constructor: bool
                                  └──Type expr: Constructor: string
                            └──Desc: Variable
                               └──Variable: is_positive
                         └──Expression:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Int
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: int
                                  └──Type expr: Row cons
                                     └──Label: Float
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: float
                                     └──Type expr: Row cons
                                        └──Label: Rational
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Constructor: int
                                              └──Type expr: Constructor: int
                                        └──Type expr: Variable: 139
                            └──Desc: Variant
                               └──Variant description:
                                  └──Tag: Rational
                                  └──Variant row:
                                     └──Type expr: Row cons
                                        └──Label: Int
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: int
                                        └──Type expr: Row cons
                                           └──Label: Float
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: float
                                           └──Type expr: Row cons
                                              └──Label: Rational
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: int
                                              └──Type expr: Variable: 139
                               └──Expression:
                                  └──Type expr: Tuple
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                                  └──Desc: Tuple
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 3
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 4 |}]


let%expect_test "" =
  let str =
    {|
      (* Dromedary doesn't yet support alias variants, so no type defs *)

      let basic_color_to_int = 
        fun basic_color ->
          match basic_color with
          ( `Black -> 0 | `Red -> 1 | `Green -> 2 | `Yellow -> 3
          | `Blue -> 4 | `Megenta -> 5 | `Cyan -> 6 | `While -> 7
          )
      ;;

      let color_to_int = 
        fun color ->
          match color with
          ( `Basic (basic_color, weight) ->
            let base = match weight with (`Bold -> 8 | `Regular -> 0) in
            base + basic_color_to_int basic_color
          | `Rgb (r, g, b) -> 16 + b + g * 6 + r * 36
          | `Gray i -> 232 + i
          )
      ;;

      let extended_color_to_int = 
        fun ex_color -> 
          match ex_color with
          ( `Rgba (r, g, b, a) -> 256 + a + b * 6 + g * 36 + r * 216
          | color -> color_to_int color 
          )
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Black
                            └──Type expr: Constructor: present
                               └──Type expr: Constructor: unit
                            └──Type expr: Row cons
                               └──Label: Red
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Row cons
                                  └──Label: Green
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row cons
                                     └──Label: Yellow
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: Blue
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Megenta
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row cons
                                              └──Label: Cyan
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: While
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                      └──Type expr: Constructor: int
                   └──Desc: Variable: basic_color_to_int
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Black
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Row cons
                                  └──Label: Red
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row cons
                                     └──Label: Green
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: Yellow
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Blue
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row cons
                                              └──Label: Megenta
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Cyan
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: While
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Black
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row cons
                                     └──Label: Red
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: Green
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Yellow
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row cons
                                              └──Label: Blue
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Megenta
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Cyan
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: While
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                            └──Desc: Variable: basic_color
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Black
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Red
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row cons
                                              └──Label: Green
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Yellow
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Blue
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Megenta
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Cyan
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: While
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                  └──Desc: Variable
                                     └──Variable: basic_color
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Black
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: Red
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Green
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row cons
                                              └──Label: Yellow
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Blue
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Megenta
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Cyan
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: While
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Black
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Red
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Green
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Yellow
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Blue
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Megenta
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Cyan
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: While
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Black
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Black
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Red
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Green
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Yellow
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Blue
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Megenta
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cyan
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: While
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 0
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Black
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Red
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Green
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Yellow
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Blue
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Megenta
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Cyan
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: While
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Red
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Black
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Red
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Green
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Yellow
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Blue
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Megenta
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cyan
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: While
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 1
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Black
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Red
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Green
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Yellow
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Blue
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Megenta
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Cyan
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: While
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Green
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Black
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Red
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Green
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Yellow
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Blue
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Megenta
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cyan
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: While
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 2
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Black
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Red
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Green
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Yellow
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Blue
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Megenta
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Cyan
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: While
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Yellow
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Black
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Red
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Green
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Yellow
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Blue
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Megenta
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cyan
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: While
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 3
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Black
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Red
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Green
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Yellow
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Blue
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Megenta
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Cyan
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: While
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Blue
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Black
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Red
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Green
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Yellow
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Blue
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Megenta
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cyan
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: While
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 4
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Black
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Red
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Green
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Yellow
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Blue
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Megenta
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Cyan
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: While
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Megenta
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Black
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Red
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Green
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Yellow
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Blue
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Megenta
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cyan
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: While
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 5
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Black
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Red
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Green
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Yellow
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Blue
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Megenta
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Cyan
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: While
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Cyan
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Black
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Red
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Green
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Yellow
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Blue
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Megenta
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cyan
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: While
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 6
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Black
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Red
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Green
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Yellow
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Blue
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Megenta
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Cyan
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: While
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: While
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Black
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Red
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Green
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Yellow
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Blue
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Megenta
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cyan
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: While
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 7
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Basic
                            └──Type expr: Constructor: present
                               └──Type expr: Tuple
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Black
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Red
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row cons
                                              └──Label: Green
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Yellow
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Blue
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Megenta
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Cyan
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: While
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Bold
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row cons
                                           └──Label: Regular
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                            └──Type expr: Row cons
                               └──Label: Rgb
                               └──Type expr: Constructor: present
                                  └──Type expr: Tuple
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                               └──Type expr: Row cons
                                  └──Label: Gray
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: int
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                      └──Type expr: Constructor: int
                   └──Desc: Variable: color_to_int
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Basic
                               └──Type expr: Constructor: present
                                  └──Type expr: Tuple
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Black
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row cons
                                              └──Label: Red
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Green
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Yellow
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Blue
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Megenta
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Cyan
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: While
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row uniform
                                                                   └──Type expr: Constructor: absent
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Bold
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row cons
                                              └──Label: Regular
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                               └──Type expr: Row cons
                                  └──Label: Rgb
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: int
                                        └──Type expr: Constructor: int
                                        └──Type expr: Constructor: int
                                  └──Type expr: Row cons
                                     └──Label: Gray
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: int
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Basic
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Black
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Red
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Green
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Yellow
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Blue
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Megenta
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Cyan
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: While
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Bold
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Regular
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                  └──Type expr: Row cons
                                     └──Label: Rgb
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: int
                                     └──Type expr: Row cons
                                        └──Label: Gray
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: int
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                            └──Desc: Variable: color
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Basic
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Black
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Red
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Green
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Yellow
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Blue
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Megenta
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cyan
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: While
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Bold
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Regular
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                        └──Type expr: Row cons
                                           └──Label: Rgb
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                           └──Type expr: Row cons
                                              └──Label: Gray
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                                  └──Desc: Variable
                                     └──Variable: color
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Basic
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Black
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Red
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Green
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Yellow
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Blue
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Megenta
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Cyan
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: While
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Bold
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Regular
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                     └──Type expr: Row cons
                                        └──Label: Rgb
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Constructor: int
                                              └──Type expr: Constructor: int
                                              └──Type expr: Constructor: int
                                        └──Type expr: Row cons
                                           └──Label: Gray
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: int
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Basic
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Black
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Red
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Green
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Yellow
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Blue
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: Megenta
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cyan
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: While
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Bold
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Regular
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                              └──Type expr: Row cons
                                                 └──Label: Rgb
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Constructor: int
                                                 └──Type expr: Row cons
                                                    └──Label: Gray
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Basic
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Basic
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Black
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Red
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Green
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: Yellow
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Blue
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: Megenta
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cyan
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: While
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Row uniform
                                                                                        └──Type expr: Constructor: absent
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Bold
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Regular
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                    └──Type expr: Row cons
                                                       └──Label: Rgb
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: int
                                                       └──Type expr: Row cons
                                                          └──Label: Gray
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Black
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Red
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Green
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Yellow
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Blue
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Megenta
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cyan
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: While
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row uniform
                                                                               └──Type expr: Constructor: absent
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Bold
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Regular
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Black
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Red
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Green
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Yellow
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Blue
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: Megenta
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cyan
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: While
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                                                    └──Desc: Variable: basic_color
                                                 └──Pattern:
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Bold
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Regular
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                                    └──Desc: Variable: weight
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Let
                                           └──Value bindings:
                                              └──Value binding:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable: base
                                                 └──Abstraction:
                                                    └──Variables:
                                                    └──Expression:
                                                       └──Type expr: Constructor: int
                                                       └──Desc: Match
                                                          └──Expression:
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Bold
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Regular
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                             └──Desc: Variable
                                                                └──Variable: weight
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Bold
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Regular
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                          └──Cases:
                                                             └──Case:
                                                                └──Pattern:
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Bold
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Regular
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row uniform
                                                                               └──Type expr: Constructor: absent
                                                                   └──Desc: Variant
                                                                      └──Variant description:
                                                                         └──Tag: Bold
                                                                         └──Variant row:
                                                                            └──Type expr: Row cons
                                                                               └──Label: Bold
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Regular
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row uniform
                                                                                     └──Type expr: Constructor: absent
                                                                └──Expression:
                                                                   └──Type expr: Constructor: int
                                                                   └──Desc: Constant: 8
                                                             └──Case:
                                                                └──Pattern:
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Bold
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Regular
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row uniform
                                                                               └──Type expr: Constructor: absent
                                                                   └──Desc: Variant
                                                                      └──Variant description:
                                                                         └──Tag: Regular
                                                                         └──Variant row:
                                                                            └──Type expr: Row cons
                                                                               └──Label: Bold
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Regular
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row uniform
                                                                                     └──Type expr: Constructor: absent
                                                                └──Expression:
                                                                   └──Type expr: Constructor: int
                                                                   └──Desc: Constant: 0
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
                                                             └──Variable: base
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Black
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Red
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: Green
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Yellow
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: Blue
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Megenta
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cyan
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: While
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Row uniform
                                                                                           └──Type expr: Constructor: absent
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: basic_color_to_int
                                                       └──Expression:
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Black
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Red
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Green
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: Yellow
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Blue
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: Megenta
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cyan
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: While
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Row uniform
                                                                                        └──Type expr: Constructor: absent
                                                          └──Desc: Variable
                                                             └──Variable: basic_color
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Basic
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Black
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Red
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Green
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Yellow
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Blue
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: Megenta
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cyan
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: While
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Bold
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Regular
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                              └──Type expr: Row cons
                                                 └──Label: Rgb
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Constructor: int
                                                 └──Type expr: Row cons
                                                    └──Label: Gray
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Rgb
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Basic
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Black
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Red
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Green
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: Yellow
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Blue
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: Megenta
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cyan
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: While
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Row uniform
                                                                                        └──Type expr: Constructor: absent
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Bold
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Regular
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                    └──Type expr: Row cons
                                                       └──Label: Rgb
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: int
                                                       └──Type expr: Row cons
                                                          └──Label: Gray
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable: r
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable: g
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable: b
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
                                                                            └──Desc: Constant: 16
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Variable
                                                                         └──Variable: b
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
                                                                      └──Desc: Primitive: (*)
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Variable
                                                                         └──Variable: g
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Constant: 6
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
                                                          └──Desc: Primitive: (*)
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: r
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 36
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Basic
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Black
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Red
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Green
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Yellow
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Blue
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: Megenta
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cyan
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: While
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Bold
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Regular
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                              └──Type expr: Row cons
                                                 └──Label: Rgb
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Constructor: int
                                                 └──Type expr: Row cons
                                                    └──Label: Gray
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Gray
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Basic
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Black
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Red
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Green
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: Yellow
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Blue
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: Megenta
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cyan
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: While
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Row uniform
                                                                                        └──Type expr: Constructor: absent
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Bold
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Regular
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                    └──Type expr: Row cons
                                                       └──Label: Rgb
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: int
                                                       └──Type expr: Row cons
                                                          └──Label: Gray
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                           └──Pattern:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable: i
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
                                                    └──Desc: Constant: 232
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: i
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variant
                         └──Type expr: Row cons
                            └──Label: Rgba
                            └──Type expr: Constructor: present
                               └──Type expr: Tuple
                                  └──Type expr: Constructor: int
                                  └──Type expr: Constructor: int
                                  └──Type expr: Constructor: int
                                  └──Type expr: Constructor: int
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Basic
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Black
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Red
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Green
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Yellow
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Blue
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Megenta
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Cyan
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: While
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Bold
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row cons
                                                 └──Label: Regular
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                  └──Type expr: Row cons
                                     └──Label: Rgb
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: int
                                     └──Type expr: Row cons
                                        └──Label: Gray
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: int
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                      └──Type expr: Constructor: int
                   └──Desc: Variable: extended_color_to_int
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Rgba
                               └──Type expr: Constructor: present
                                  └──Type expr: Tuple
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Basic
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Black
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Red
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Green
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Yellow
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Blue
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Megenta
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Cyan
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: While
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Bold
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row cons
                                                    └──Label: Regular
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                     └──Type expr: Row cons
                                        └──Label: Rgb
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Constructor: int
                                              └──Type expr: Constructor: int
                                              └──Type expr: Constructor: int
                                        └──Type expr: Row cons
                                           └──Label: Gray
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: int
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Rgba
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: int
                                        └──Type expr: Constructor: int
                                        └──Type expr: Constructor: int
                                        └──Type expr: Constructor: int
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Basic
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Black
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Red
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Green
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Yellow
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Blue
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Megenta
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cyan
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: While
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Bold
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Regular
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                        └──Type expr: Row cons
                                           └──Label: Rgb
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                           └──Type expr: Row cons
                                              └──Label: Gray
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                            └──Desc: Variable: ex_color
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Rgba
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Constructor: int
                                              └──Type expr: Constructor: int
                                              └──Type expr: Constructor: int
                                              └──Type expr: Constructor: int
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Basic
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Black
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Red
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Green
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Yellow
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Blue
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: Megenta
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cyan
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: While
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Bold
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Regular
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                              └──Type expr: Row cons
                                                 └──Label: Rgb
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Constructor: int
                                                 └──Type expr: Row cons
                                                    └──Label: Gray
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                  └──Desc: Variable
                                     └──Variable: ex_color
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Rgba
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: int
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Basic
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Black
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Red
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Green
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Yellow
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Blue
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Megenta
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cyan
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: While
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row uniform
                                                                               └──Type expr: Constructor: absent
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Bold
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Regular
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                           └──Type expr: Row cons
                                              └──Label: Rgb
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: int
                                              └──Type expr: Row cons
                                                 └──Label: Gray
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Rgba
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: int
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Basic
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Black
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Red
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Green
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: Yellow
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Blue
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: Megenta
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cyan
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: While
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Row uniform
                                                                                        └──Type expr: Constructor: absent
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Bold
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Regular
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                    └──Type expr: Row cons
                                                       └──Label: Rgb
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: int
                                                       └──Type expr: Row cons
                                                          └──Label: Gray
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Rgba
                                              └──Variant row:
                                                 └──Type expr: Row cons
                                                    └──Label: Rgba
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: int
                                                          └──Type expr: Constructor: int
                                                          └──Type expr: Constructor: int
                                                          └──Type expr: Constructor: int
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Basic
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Black
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: Red
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Green
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: Yellow
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Blue
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Megenta
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Cyan
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: While
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Constructor: unit
                                                                                           └──Type expr: Row uniform
                                                                                              └──Type expr: Constructor: absent
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Bold
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: Regular
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                                          └──Type expr: Row cons
                                                             └──Label: Rgb
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: int
                                                                   └──Type expr: Constructor: int
                                                                   └──Type expr: Constructor: int
                                                             └──Type expr: Row cons
                                                                └──Label: Gray
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: int
                                                                └──Type expr: Row uniform
                                                                   └──Type expr: Constructor: absent
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable: r
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable: g
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable: b
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable: a
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
                                                                                        └──Desc: Constant: 256
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: int
                                                                                  └──Desc: Variable
                                                                                     └──Variable: a
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
                                                                                  └──Desc: Primitive: (*)
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: int
                                                                                  └──Desc: Variable
                                                                                     └──Variable: b
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: int
                                                                            └──Desc: Constant: 6
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
                                                                      └──Desc: Primitive: (*)
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Variable
                                                                         └──Variable: g
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Constant: 36
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
                                                          └──Desc: Primitive: (*)
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: r
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 216
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Rgba
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: int
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Basic
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Black
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Red
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Green
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: Yellow
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Blue
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: Megenta
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cyan
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: While
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Row uniform
                                                                                        └──Type expr: Constructor: absent
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Bold
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Regular
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                    └──Type expr: Row cons
                                                       └──Label: Rgb
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: int
                                                       └──Type expr: Row cons
                                                          └──Label: Gray
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                        └──Desc: Variable: color
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Basic
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Black
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Red
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: Green
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Yellow
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: Blue
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Megenta
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cyan
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: While
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Row uniform
                                                                                           └──Type expr: Constructor: absent
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Bold
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Regular
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                       └──Type expr: Row cons
                                                          └──Label: Rgb
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: int
                                                          └──Type expr: Row cons
                                                             └──Label: Gray
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: int
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                                 └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: color_to_int
                                           └──Expression:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Basic
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Black
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Red
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row cons
                                                                      └──Label: Green
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: Yellow
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Blue
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: Megenta
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cyan
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: While
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Row uniform
                                                                                        └──Type expr: Constructor: absent
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Bold
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Regular
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                    └──Type expr: Row cons
                                                       └──Label: Rgb
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: int
                                                       └──Type expr: Row cons
                                                          └──Label: Gray
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                              └──Desc: Variable
                                                 └──Variable: color |}]
