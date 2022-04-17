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
                   └──Constructor alphas: 16899 16900
                   └──Constructor type:
                      └──Type expr: Constructor: var
                         └──Type expr: Variable: 16899
                         └──Type expr: Variable: 16900
                   └──Constructor argument:
                      └──Constructor betas: 16901
                      └──Type expr: Constructor: unit
                   └──Constraint:
                      └──Type expr: Variable: 16899
                      └──Type expr: Tuple
                         └──Type expr: Variable: 16900
                         └──Type expr: Variable: 16901
                └──Constructor declaration:
                   └──Constructor name: Succ
                   └──Constructor alphas: 16899 16900
                   └──Constructor type:
                      └──Type expr: Constructor: var
                         └──Type expr: Variable: 16899
                         └──Type expr: Variable: 16900
                   └──Constructor argument:
                      └──Constructor betas: 16906 16905
                      └──Type expr: Constructor: var
                         └──Type expr: Variable: 16905
                         └──Type expr: Variable: 16900
                   └──Constraint:
                      └──Type expr: Variable: 16899
                      └──Type expr: Tuple
                         └──Type expr: Variable: 16906
                         └──Type expr: Variable: 16905
       └──Structure item: Type
          └──Type declaration:
             └──Type name: ty
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Int
                   └──Constructor alphas: 16910 16911
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 16910
                         └──Type expr: Variable: 16911
                   └──Constraint:
                      └──Type expr: Variable: 16911
                      └──Type expr: Constructor: int
                └──Constructor declaration:
                   └──Constructor name: Bool
                   └──Constructor alphas: 16910 16911
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 16910
                         └──Type expr: Variable: 16911
                   └──Constraint:
                      └──Type expr: Variable: 16911
                      └──Type expr: Constructor: bool
                └──Constructor declaration:
                   └──Constructor name: Var
                   └──Constructor alphas: 16910 16911
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 16910
                         └──Type expr: Variable: 16911
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: var
                         └──Type expr: Variable: 16910
                         └──Type expr: Variable: 16911
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 16928
                         └──Type expr: Variable: 16929
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 16928
                            └──Type expr: Variable: 16929
                         └──Type expr: Constructor: int
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: 16929,16928
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 16928
                            └──Type expr: Variable: 16929
                         └──Type expr: Arrow
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: 16928
                               └──Type expr: Variable: 16929
                            └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: 16928
                               └──Type expr: Variable: 16929
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: ty
                                  └──Type expr: Variable: 16928
                                  └──Type expr: Variable: 16929
                               └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: ty
                                     └──Type expr: Variable: 16928
                                     └──Type expr: Variable: 16929
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: ty
                                              └──Type expr: Variable: 16928
                                              └──Type expr: Variable: 16929
                                           └──Type expr: Constructor: ty
                                              └──Type expr: Variable: 16928
                                              └──Type expr: Variable: 16929
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: 16928
                                                 └──Type expr: Variable: 16929
                                              └──Desc: Variable
                                                 └──Variable: t1
                                           └──Expression:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: 16928
                                                 └──Type expr: Variable: 16929
                                              └──Desc: Variable
                                                 └──Variable: t2
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: ty
                                           └──Type expr: Variable: 16928
                                           └──Type expr: Variable: 16929
                                        └──Type expr: Constructor: ty
                                           └──Type expr: Variable: 16928
                                           └──Type expr: Variable: 16929
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 16928
                                                    └──Type expr: Variable: 16929
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 16928
                                                    └──Type expr: Variable: 16929
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 16928
                                                       └──Type expr: Variable: 16929
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 16928
                                                                └──Type expr: Variable: 16929
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 16928
                                                       └──Type expr: Variable: 16929
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 16928
                                                                └──Type expr: Variable: 16929
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 0
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 16928
                                                    └──Type expr: Variable: 16929
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 16928
                                                    └──Type expr: Variable: 16929
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 16928
                                                       └──Type expr: Variable: 16929
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Bool
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 16928
                                                                └──Type expr: Variable: 16929
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 16928
                                                       └──Type expr: Variable: 16929
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Bool
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 16928
                                                                └──Type expr: Variable: 16929
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 1
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 16928
                                                    └──Type expr: Variable: 16929
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 16928
                                                    └──Type expr: Variable: 16929
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 16928
                                                       └──Type expr: Variable: 16929
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Var
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Variable: 16928
                                                                └──Type expr: Variable: 16929
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 16928
                                                                └──Type expr: Variable: 16929
                                                       └──Pattern:
                                                          └──Type expr: Constructor: var
                                                             └──Type expr: Variable: 16928
                                                             └──Type expr: Variable: 16929
                                                          └──Desc: Variable: var
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 16928
                                                       └──Type expr: Variable: 16929
                                                    └──Desc: Any
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 2 |}]