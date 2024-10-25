open! Import
open Util

let%expect_test "" =
  let str =
    {|
      type 'a t = 
        | Int constraint 'a = int
      ;;

      external ignore : 'a. 'a -> unit = "%ignore";;

      let (type 'a) f = 
        fun (x : 'a t) (y : int) ->
          match x with
          ( Int -> ignore (y : 'a); () )
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
                   └──Constructor name: Int
                   └──Constructor alphas: 20
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 20
                   └──Constraint:
                      └──Type expr: Variable: 20
                      └──Type expr: Constructor: int
       └──Structure item: Primitive
          └──Value description:
             └──Name: ignore
             └──Scheme:
                └──Variables: 0
                └──Type expr: Arrow
                   └──Type expr: Variable: 0
                   └──Type expr: Constructor: unit
             └──Primitive name: %ignore
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 14
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: unit
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: 14
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: 14
                         └──Type expr: Arrow
                            └──Type expr: Constructor: int
                            └──Type expr: Constructor: unit
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: 14
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Constructor: unit
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Constructor: unit
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: 14
                                        └──Desc: Variable
                                           └──Variable: x
                                     └──Type expr: Constructor: t
                                        └──Type expr: Variable: 14
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: 14
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Int
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: 14
                                           └──Expression:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Sequence
                                                 └──Expression:
                                                    └──Type expr: Constructor: unit
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 14
                                                             └──Type expr: Constructor: unit
                                                          └──Desc: Variable
                                                             └──Variable: ignore
                                                             └──Type expr: Variable: 14
                                                       └──Expression:
                                                          └──Type expr: Variable: 14
                                                          └──Desc: Variable
                                                             └──Variable: y
                                                 └──Expression:
                                                    └──Type expr: Constructor: unit
                                                    └──Desc: Constant: () |}]


let%expect_test "" =
  let str =
    {|
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      type 'a list = 
        | Nil
        | Cons of 'a * 'a list
      ;;

      let (type 'a 'b) fails = 
        fun (x : ('a, 'b) eq) ->
          match (x, Nil) with
          ( (Refl, Cons ((_ : 'a), Nil) ) -> Nil 
          | (Refl, Cons ((_ : 'b), Nil) ) -> Nil
          )
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    ("Cannot unify types" ("Type_expr.decode type_expr1" (Type 51 (Var 51)))
     ("Type_expr.decode type_expr2" (Type 72 (Var 72)))) |}]


let%expect_test "" =
  let str =
    {|
      type 'a list = 
        | Nil
        | Cons of 'a * 'a list
      ;;

      let x =
        match Nil with
        ( Cons ("1", Nil) -> 1
        | Cons (1.0, Nil) -> 2
        | Cons (1, Nil) -> 3
        | _ -> 4
        )
      ;; 
    |}
  in
  print_infer_result str;
  [%expect
    {|
    ("Cannot unify types"
     ("Type_expr.decode type_expr1" (Type 23 (Former (Constr () string))))
     ("Type_expr.decode type_expr2" (Type 37 (Former (Constr () float))))) |}]
