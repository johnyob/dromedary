open! Import
open Util

let%expect_test "" = 
  let str = 
    {|
      type ('env, 'a) var = 
        | Zero of 'env1. unit constraint 'env = 'a * 'env1
        | Succ of 'env1 'b. ('env1, 'a) var constraint 'env = 'b * 'env1
      ;;

      type ('env, 'a) ty = 
        | Int constraint 'a = int
        | Bool constraint 'a = bool
        | Var of ('env, 'a) var
      ;;

      let (type 'env 'a) f = 
        fun (t1 : ('env, 'a) ty) (t2 : ('env, 'a) ty) ->
          (match (t1, t2) with
           ( (Int, Int) -> 0
           | (Bool, Bool) -> 1
           | (Var var, _) -> 2
           (* Dromedary doesn't support unreachable case analysis *)
           )
          : int)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: var
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Zero
                   └──Constructor alphas: env a
                   └──Constructor type:
                      └──Type expr: Constructor: var
                         └──Type expr: Variable: env
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas: env1
                      └──Type expr: Constructor: unit
                   └──Constraint:
                      └──Type expr: Variable: env
                      └──Type expr: Tuple
                         └──Type expr: Variable: a
                         └──Type expr: Variable: env1
                └──Constructor declaration:
                   └──Constructor name: Succ
                   └──Constructor alphas: env a
                   └──Constructor type:
                      └──Type expr: Constructor: var
                         └──Type expr: Variable: env
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas: env1 b
                      └──Type expr: Constructor: var
                         └──Type expr: Variable: env1
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: env
                      └──Type expr: Tuple
                         └──Type expr: Variable: b
                         └──Type expr: Variable: env1
       └──Structure item: Type
          └──Type declaration:
             └──Type name: ty
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Int
                   └──Constructor alphas: env a
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: env
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: int
                └──Constructor declaration:
                   └──Constructor name: Bool
                   └──Constructor alphas: env a
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: env
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: bool
                └──Constructor declaration:
                   └──Constructor name: Var
                   └──Constructor alphas: env a
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: env
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: var
                         └──Type expr: Variable: env
                         └──Type expr: Variable: a
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: a16214
                         └──Type expr: Variable: a16215
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: a16214
                            └──Type expr: Variable: a16215
                         └──Type expr: Constructor: int
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: a16215,a16214
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: a16214
                            └──Type expr: Variable: a16215
                         └──Type expr: Arrow
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: a16214
                               └──Type expr: Variable: a16215
                            └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: a16214
                               └──Type expr: Variable: a16215
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: ty
                                  └──Type expr: Variable: a16214
                                  └──Type expr: Variable: a16215
                               └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: ty
                                     └──Type expr: Variable: a16214
                                     └──Type expr: Variable: a16215
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: ty
                                              └──Type expr: Variable: a16214
                                              └──Type expr: Variable: a16215
                                           └──Type expr: Constructor: ty
                                              └──Type expr: Variable: a16214
                                              └──Type expr: Variable: a16215
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: a16214
                                                 └──Type expr: Variable: a16215
                                              └──Desc: Variable
                                                 └──Variable: t1
                                           └──Expression:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: a16214
                                                 └──Type expr: Variable: a16215
                                              └──Desc: Variable
                                                 └──Variable: t2
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: ty
                                           └──Type expr: Variable: a16214
                                           └──Type expr: Variable: a16215
                                        └──Type expr: Constructor: ty
                                           └──Type expr: Variable: a16214
                                           └──Type expr: Variable: a16215
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a16214
                                                    └──Type expr: Variable: a16215
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a16214
                                                    └──Type expr: Variable: a16215
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a16214
                                                       └──Type expr: Variable: a16215
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a16214
                                                                └──Type expr: Variable: a16215
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a16214
                                                       └──Type expr: Variable: a16215
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a16214
                                                                └──Type expr: Variable: a16215
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 0
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a16214
                                                    └──Type expr: Variable: a16215
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a16214
                                                    └──Type expr: Variable: a16215
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a16214
                                                       └──Type expr: Variable: a16215
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Bool
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a16214
                                                                └──Type expr: Variable: a16215
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a16214
                                                       └──Type expr: Variable: a16215
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Bool
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a16214
                                                                └──Type expr: Variable: a16215
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 1
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a16214
                                                    └──Type expr: Variable: a16215
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a16214
                                                    └──Type expr: Variable: a16215
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a16214
                                                       └──Type expr: Variable: a16215
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Var
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Variable: a16214
                                                                └──Type expr: Variable: a16215
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a16214
                                                                └──Type expr: Variable: a16215
                                                       └──Pattern:
                                                          └──Type expr: Constructor: var
                                                             └──Type expr: Variable: a16214
                                                             └──Type expr: Variable: a16215
                                                          └──Desc: Variable: var
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a16214
                                                       └──Type expr: Variable: a16215
                                                    └──Desc: Any
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 2 |}]