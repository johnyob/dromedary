open! Import
open Util

(* Tests from typing-gadts/didier.ml
   -------------------------------------------
   Test count: 5/7
   
   2 test are removed due to reliance 
   on exhaustive pattern matching.
*)

let%expect_test "didier-1" =
  let str =
    {|
      type 'a ty = 
        | Int constraint 'a = int
        | Bool constraint 'a = bool
      ;;

      let (type 't) f = 
        fun (x : 't) (tag : 't ty) ->
          match tag with
          ( Int -> x = 0
          | Bool -> x
          )
      ;; 
    |}
  in
  print_infer_result str;
  [%expect
    {|
    ("Type escape it's equational scope"
     ("Type_expr.decode type_expr" (Type 29796 (Var 29796)))) |}]

let%expect_test "didier-2" =
  let str =
    {|
      type 'a ty = 
        | Int constraint 'a = int
        | Bool constraint 'a = bool
      ;;

      let (type 't) g =
        fun (x : 't) (tag : 't ty) ->
          match tag with
          ( Bool -> x
          | Int -> x = 1
          )
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    ("Cannot unify types"
     ("Type_expr.decode type_expr1"
      (Type 29874
       (Former
        (Arrow (Type 29873 (Former (Constr () int)))
         (Type 29871
          (Former
           (Arrow (Type 29870 (Former (Constr () int))) (Type 29851 (Var 29851)))))))))
     ("Type_expr.decode type_expr2"
      (Type 29880
       (Former
        (Arrow (Type 29873 (Former (Constr () int)))
         (Type 29878
          (Former
           (Arrow (Type 29870 (Former (Constr () int)))
            (Type 29876 (Former (Constr () bool))))))))))) |}]

let%expect_test "didier-3" =
  let str =
    {|
      type 'a ty = 
        | Int constraint 'a = int
        | Bool constraint 'a = bool
      ;;

      let (type 't) g = 
        fun (x : 't) (tag : 't ty) ->
          (match tag with
           ( Bool -> x
           | Int -> x = 0
           ) 
          : bool
          )
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
             └──Type name: ty
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Int
                   └──Constructor alphas: 29888
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 29888
                   └──Constraint:
                      └──Type expr: Variable: 29888
                      └──Type expr: Constructor: int
                └──Constructor declaration:
                   └──Constructor name: Bool
                   └──Constructor alphas: 29888
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 29888
                   └──Constraint:
                      └──Type expr: Variable: 29888
                      └──Type expr: Constructor: bool
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 29898
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 29898
                         └──Type expr: Constructor: bool
                   └──Desc: Variable: g
                └──Abstraction:
                   └──Variables: 29898
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 29898
                         └──Type expr: Arrow
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: 29898
                            └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 29898
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: ty
                                  └──Type expr: Variable: 29898
                               └──Type expr: Constructor: bool
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: ty
                                     └──Type expr: Variable: 29898
                                  └──Desc: Variable: tag
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: ty
                                           └──Type expr: Variable: 29898
                                        └──Desc: Variable
                                           └──Variable: tag
                                     └──Type expr: Constructor: ty
                                        └──Type expr: Variable: 29898
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: 29898
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Bool
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: 29898
                                           └──Expression:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Variable
                                                 └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: 29898
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Int
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: 29898
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
                                                             └──Type expr: Variable: 29898
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: bool
                                                          └──Desc: Primitive: (=)
                                                       └──Expression:
                                                          └──Type expr: Variable: 29898
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 0 |}]

let%expect_test "didier-4" =
  let str =
    {|
      type 'a ty = 
        | Int constraint 'a = int
        | Bool constraint 'a = bool
      ;;

      let id = fun x -> x;;
      let idb1 = (fun id -> let _ = id true in id) id;;
      let idb2 = (id : bool -> bool);;
      let idb3 = fun (_ : bool) -> false;; 

      let (type 't) g = 
        fun (x : 't) (tag : 't ty) ->
          match tag with
          ( Bool -> idb3 x
          | Int -> x = 0
          )
      ;;

      let (type 't) g = 
        fun (x : 't) (tag : 't ty) ->
          match tag with
          ( Bool -> idb2 x
          | Int -> x = 0
          )
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
             └──Type name: ty
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Int
                   └──Constructor alphas: 29956
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 29956
                   └──Constraint:
                      └──Type expr: Variable: 29956
                      └──Type expr: Constructor: int
                └──Constructor declaration:
                   └──Constructor name: Bool
                   └──Constructor alphas: 29956
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 29956
                   └──Constraint:
                      └──Type expr: Variable: 29956
                      └──Type expr: Constructor: bool
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 29963
                      └──Type expr: Variable: 29963
                   └──Desc: Variable: id
                └──Abstraction:
                   └──Variables: 29963,29963
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 29963
                         └──Type expr: Variable: 29963
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 29963
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: 29963
                            └──Desc: Variable
                               └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: bool
                      └──Type expr: Constructor: bool
                   └──Desc: Variable: idb1
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: bool
                         └──Type expr: Constructor: bool
                      └──Desc: Application
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: bool
                                  └──Type expr: Constructor: bool
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: bool
                                  └──Type expr: Constructor: bool
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: bool
                                     └──Type expr: Constructor: bool
                                  └──Desc: Variable: id
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: bool
                                     └──Type expr: Constructor: bool
                                  └──Desc: Let
                                     └──Value bindings:
                                        └──Value binding:
                                           └──Pattern:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Any
                                           └──Abstraction:
                                              └──Variables:
                                              └──Expression:
                                                 └──Type expr: Constructor: bool
                                                 └──Desc: Application
                                                    └──Expression:
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: bool
                                                          └──Type expr: Constructor: bool
                                                       └──Desc: Variable
                                                          └──Variable: id
                                                    └──Expression:
                                                       └──Type expr: Constructor: bool
                                                       └──Desc: Constant: true
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: bool
                                           └──Type expr: Constructor: bool
                                        └──Desc: Variable
                                           └──Variable: id
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: bool
                               └──Type expr: Constructor: bool
                            └──Desc: Variable
                               └──Variable: id
                               └──Type expr: Constructor: bool
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: bool
                      └──Type expr: Constructor: bool
                   └──Desc: Variable: idb2
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: bool
                         └──Type expr: Constructor: bool
                      └──Desc: Variable
                         └──Variable: id
                         └──Type expr: Constructor: bool
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: bool
                      └──Type expr: Constructor: bool
                   └──Desc: Variable: idb3
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: bool
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: bool
                            └──Desc: Any
                         └──Expression:
                            └──Type expr: Constructor: bool
                            └──Desc: Constant: false
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 30013
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 30013
                         └──Type expr: Constructor: bool
                   └──Desc: Variable: g
                └──Abstraction:
                   └──Variables: 30013
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 30013
                         └──Type expr: Arrow
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: 30013
                            └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 30013
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: ty
                                  └──Type expr: Variable: 30013
                               └──Type expr: Constructor: bool
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: ty
                                     └──Type expr: Variable: 30013
                                  └──Desc: Variable: tag
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: ty
                                           └──Type expr: Variable: 30013
                                        └──Desc: Variable
                                           └──Variable: tag
                                     └──Type expr: Constructor: ty
                                        └──Type expr: Variable: 30013
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: 30013
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Bool
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: 30013
                                           └──Expression:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 30013
                                                       └──Type expr: Constructor: bool
                                                    └──Desc: Variable
                                                       └──Variable: idb3
                                                 └──Expression:
                                                    └──Type expr: Variable: 30013
                                                    └──Desc: Variable
                                                       └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: 30013
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Int
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: 30013
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
                                                             └──Type expr: Variable: 30013
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: bool
                                                          └──Desc: Primitive: (=)
                                                       └──Expression:
                                                          └──Type expr: Variable: 30013
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 0
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 30070
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 30070
                         └──Type expr: Constructor: bool
                   └──Desc: Variable: g
                └──Abstraction:
                   └──Variables: 30070
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 30070
                         └──Type expr: Arrow
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: 30070
                            └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 30070
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: ty
                                  └──Type expr: Variable: 30070
                               └──Type expr: Constructor: bool
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: ty
                                     └──Type expr: Variable: 30070
                                  └──Desc: Variable: tag
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: ty
                                           └──Type expr: Variable: 30070
                                        └──Desc: Variable
                                           └──Variable: tag
                                     └──Type expr: Constructor: ty
                                        └──Type expr: Variable: 30070
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: 30070
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Bool
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: 30070
                                           └──Expression:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 30070
                                                       └──Type expr: Constructor: bool
                                                    └──Desc: Variable
                                                       └──Variable: idb2
                                                 └──Expression:
                                                    └──Type expr: Variable: 30070
                                                    └──Desc: Variable
                                                       └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: 30070
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Int
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: 30070
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
                                                             └──Type expr: Variable: 30070
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: bool
                                                          └──Desc: Primitive: (=)
                                                       └──Expression:
                                                          └──Type expr: Variable: 30070
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 0 |}]
