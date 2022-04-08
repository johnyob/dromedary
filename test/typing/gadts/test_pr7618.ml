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
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: t
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Int
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: int
       └──Structure item: Primitive
          └──Value description:
             └──Name: ignore
             └──Scheme:
                └──Variables: a5477
                └──Type expr: Arrow
                   └──Type expr: Variable: a5477
                   └──Type expr: Constructor: unit
             └──Primitive name: %ignore
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a5491
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: unit
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: a5491
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a5491
                         └──Type expr: Arrow
                            └──Type expr: Constructor: int
                            └──Type expr: Constructor: unit
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: a5491
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
                                           └──Type expr: Variable: a5491
                                        └──Desc: Variable
                                           └──Variable: x
                                     └──Type expr: Constructor: t
                                        └──Type expr: Variable: a5491
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: a5491
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Int
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a5491
                                           └──Expression:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Sequence
                                                 └──Expression:
                                                    └──Type expr: Constructor: unit
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a5491
                                                             └──Type expr: Constructor: unit
                                                          └──Desc: Variable
                                                             └──Variable: ignore
                                                             └──Type expr: Variable: a5491
                                                       └──Expression:
                                                          └──Type expr: Variable: a5491
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
  [%expect {|
    ("Cannot unify types" (type_expr1 ((desc (Ttyp_var a144))))
     (type_expr2 ((desc (Ttyp_var a145))))) |}]

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
  [%expect {|
    ("Cannot unify types" (type_expr1 ((desc (Ttyp_constr (() string)))))
     (type_expr2 ((desc (Ttyp_constr (() float)))))) |}]