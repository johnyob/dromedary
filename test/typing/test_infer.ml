open! Import
open Parsetree
open Ast_types
open Types
module Constraint = Typing.Import.Constraint

let print_constraint_result ~env exp =
  let t = Infer.Expression.infer exp |> Computation.Expression.run ~env in
  let output =
    match t with
    | Ok t -> Constraint.sexp_of_t t
    | Error err -> err
  in
  output |> Sexp.to_string_hum |> print_endline


let print_infer_result ~env exp =
  let texp = Infer.infer ~env exp in
  match texp with
  | Ok (variables, texp) ->
    let ppf = Format.std_formatter in
    Format.fprintf ppf "Variables: %s@." (String.concat ~sep:"," variables);
    Typedtree.pp_expression_mach ppf texp
  | Error err -> Sexp.to_string_hum err |> print_endline


let add_list env =
  let name = "list" in
  let params = [ "a" ] in
  let type_ = Ttyp_constr ([ Ttyp_var "a" ], name) in
  Env.add_type_decl
    env
    { type_name = name
    ; type_kind =
        Type_variant
          [ { constructor_name = "Nil"
            ; constructor_alphas = params
            ; constructor_arg = None
            ; constructor_type = type_
            ; constructor_constraints = []
            }
          ; { constructor_name = "Cons"
            ; constructor_alphas = params
            ; constructor_arg =
                Some
                  { constructor_arg_betas = []
                  ; constructor_arg_type =
                      Ttyp_tuple
                        [ Ttyp_var "a"; Ttyp_constr ([ Ttyp_var "a" ], name) ]
                  }
            ; constructor_type = type_
            ; constructor_constraints = []
            }
          ]
    }


let%expect_test "constant: int" =
  let exp = Pexp_const (Const_int 1) in
  print_infer_result ~env:Env.empty exp;
  [%expect{|
    New variable:
    id = 0, level = 0 is_generic = false, scope = 0
    New former:
    id = 1, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    Unify: 0 1
    Before exit:
    Current level: 0
    Region 0
    id = 0, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 0, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    Scope Array order:
    0,0
    Array order:
    0,0
    After exit:
    Current level: -1
    Region 0
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Constructor: int
       └──Desc: Constant: 1 |}]

let%expect_test "constant: bool" =
  let exp = Pexp_const (Const_bool true) in
  print_infer_result ~env:Env.empty exp;
  [%expect{|
    New variable:
    id = 2, level = 0 is_generic = false, scope = 0
    New former:
    id = 3, level = 0 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 0)(is_generic false))
    Unify: 2 3
    Before exit:
    Current level: 0
    Region 0
    id = 2, level = 0 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 0)(is_generic false))
    id = 2, level = 0 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 0)(is_generic false))
    Scope Array order:
    2,2
    Array order:
    2,2
    After exit:
    Current level: -1
    Region 0
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Constructor: bool
       └──Desc: Constant: true |}]

let%expect_test "constant: unit" =
  let exp = Pexp_const Const_unit in
  print_infer_result ~env:Env.empty exp;
  [%expect{|
    New variable:
    id = 4, level = 0 is_generic = false, scope = 0
    New former:
    id = 5, level = 0 is_generic = false, scope = 0
    ((structure((Constr()unit)))(level 0)(is_generic false))
    Unify: 4 5
    Before exit:
    Current level: 0
    Region 0
    id = 4, level = 0 is_generic = false, scope = 0
    ((structure((Constr()unit)))(level 0)(is_generic false))
    id = 4, level = 0 is_generic = false, scope = 0
    ((structure((Constr()unit)))(level 0)(is_generic false))
    Scope Array order:
    4,4
    Array order:
    4,4
    After exit:
    Current level: -1
    Region 0
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Constructor: unit
       └──Desc: Constant: () |}]

let%expect_test "primitives" =
  let exp =
    (* (1 + (2 / 1 - 0 * 1)) = 12 *)
    let lhs =
      let rhs =
        let lhs =
          Pexp_app
            ( Pexp_app (Pexp_prim Prim_div, Pexp_const (Const_int 2))
            , Pexp_const (Const_int 1) )
        in
        let rhs =
          Pexp_app
            ( Pexp_app (Pexp_prim Prim_mul, Pexp_const (Const_int 0))
            , Pexp_const (Const_int 1) )
        in
        Pexp_app (Pexp_app (Pexp_prim Prim_sub, lhs), rhs)
      in
      Pexp_app (Pexp_app (Pexp_prim Prim_add, Pexp_const (Const_int 1)), rhs)
    in
    Pexp_app (Pexp_app (Pexp_prim Prim_eq, lhs), Pexp_const (Const_int 12))
  in
  print_infer_result ~env:Env.empty exp;
  [%expect{|
    New variable:
    id = 6, level = 0 is_generic = false, scope = 0
    New variable:
    id = 7, level = 0 is_generic = false, scope = 0
    New former:
    id = 8, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    New variable:
    id = 9, level = 0 is_generic = false, scope = 0
    New former:
    id = 10, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    New former:
    id = 11, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    New former:
    id = 12, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    New former:
    id = 13, level = 0 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 0)(is_generic false))
    New former:
    id = 14, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()bool)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    New former:
    id = 15, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()bool)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 10 15
    New variable:
    id = 16, level = 0 is_generic = false, scope = 0
    New former:
    id = 17, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    New variable:
    id = 18, level = 0 is_generic = false, scope = 0
    New former:
    id = 19, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure((Arrow((structure())(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    New former:
    id = 20, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    New former:
    id = 21, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    New former:
    id = 22, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    New former:
    id = 23, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    New former:
    id = 24, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 19 24
    New former:
    id = 25, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    Unify: 18 25
    New variable:
    id = 26, level = 0 is_generic = false, scope = 0
    New former:
    id = 27, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    New variable:
    id = 28, level = 0 is_generic = false, scope = 0
    New former:
    id = 29, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure((Arrow((structure())(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    New former:
    id = 30, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    New former:
    id = 31, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    New former:
    id = 32, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    New former:
    id = 33, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    New former:
    id = 34, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 29 34
    New variable:
    id = 35, level = 0 is_generic = false, scope = 0
    New former:
    id = 36, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    New variable:
    id = 37, level = 0 is_generic = false, scope = 0
    New former:
    id = 38, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure((Arrow((structure())(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    New former:
    id = 39, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    New former:
    id = 40, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    New former:
    id = 41, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    New former:
    id = 42, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    New former:
    id = 43, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 38 43
    New former:
    id = 44, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    Unify: 37 44
    New former:
    id = 45, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    Unify: 35 45
    New variable:
    id = 46, level = 0 is_generic = false, scope = 0
    New former:
    id = 47, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    New variable:
    id = 48, level = 0 is_generic = false, scope = 0
    New former:
    id = 49, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure((Arrow((structure())(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    New former:
    id = 50, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    New former:
    id = 51, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    New former:
    id = 52, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    New former:
    id = 53, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    New former:
    id = 54, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 49 54
    New former:
    id = 55, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    Unify: 48 55
    New former:
    id = 56, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    Unify: 46 56
    New former:
    id = 57, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    Unify: 7 57
    Before exit:
    Current level: 0
    Region 0
    id = 38, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 29, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 35, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 46, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 7, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 37, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 46, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 9, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 10, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()bool)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 26, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 36, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 28, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 7, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 36, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 37, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 16, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 37, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 47, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 28, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 47, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 35, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 49, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 48, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 8, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()bool)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 38, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 46, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 27, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 6, level = 0 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 0)(is_generic false))
    id = 48, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 49, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 26, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 35, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 17, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 48, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 18, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 19, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    Scope Array order:
    19,18,48,17,35,26,49,48,6,27,46,38,8,48,49,35,47,28,47,37,16,37,36,7,28,36,26,10,9,46,37,7,46,35,29,38
    Array order:
    19,18,48,17,35,26,49,48,6,27,46,38,8,48,49,35,47,28,47,37,16,37,36,7,28,36,26,10,9,46,37,7,46,35,29,38
    After exit:
    Current level: -1
    Region 0
    Variables:
    Expression:
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
                               └──Desc: Constant: 1
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
                                     └──Desc: Primitive: (-)
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
                                                 └──Desc: Primitive: (/)
                                              └──Expression:
                                                 └──Type expr: Constructor: int
                                                 └──Desc: Constant: 2
                                        └──Expression:
                                           └──Type expr: Constructor: int
                                           └──Desc: Constant: 1
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
                                           └──Desc: Constant: 0
                                  └──Expression:
                                     └──Type expr: Constructor: int
                                     └──Desc: Constant: 1
          └──Expression:
             └──Type expr: Constructor: int
             └──Desc: Constant: 12 |}]

let%expect_test "function - identity" =
  let exp =
    (* fun x -> x *)
    Pexp_fun (Ppat_var "x", Pexp_var "x")
  in
  print_infer_result ~env:Env.empty exp;
  [%expect{|
    New variable:
    id = 58, level = 0 is_generic = false, scope = 0
    New variable:
    id = 59, level = 0 is_generic = false, scope = 0
    New variable:
    id = 60, level = 0 is_generic = false, scope = 0
    New former:
    id = 61, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 58 61
    Unify: 60 59
    Before exit:
    Current level: 0
    Region 0
    id = 60, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 58, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 60, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 58, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Scope Array order:
    58,60,58,60
    Array order:
    58,60,58,60
    After exit:
    Current level: -1
    Region 0
    Variables: α60
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Variable: α60
          └──Type expr: Variable: α60
       └──Desc: Function
          └──Pattern:
             └──Type expr: Variable: α60
             └──Desc: Variable: x
          └──Expression:
             └──Type expr: Variable: α60
             └──Desc: Variable
                └──Variable: x |}]

let%expect_test "function - curry" =
  let exp =
    (* fun f x y -> f (x, y) *)
    Pexp_fun
      ( Ppat_var "f"
      , Pexp_fun
          ( Ppat_var "x"
          , Pexp_fun
              ( Ppat_var "y"
              , Pexp_app
                  (Pexp_var "f", Pexp_tuple [ Pexp_var "x"; Pexp_var "y" ]) ) )
      )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect{|
    New variable:
    id = 62, level = 0 is_generic = false, scope = 0
    New variable:
    id = 63, level = 0 is_generic = false, scope = 0
    New variable:
    id = 64, level = 0 is_generic = false, scope = 0
    New former:
    id = 65, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 62 65
    New variable:
    id = 66, level = 0 is_generic = false, scope = 0
    New variable:
    id = 67, level = 0 is_generic = false, scope = 0
    New former:
    id = 68, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 64 68
    New variable:
    id = 69, level = 0 is_generic = false, scope = 0
    New variable:
    id = 70, level = 0 is_generic = false, scope = 0
    New former:
    id = 71, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 67 71
    New variable:
    id = 72, level = 0 is_generic = false, scope = 0
    New former:
    id = 73, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 73 63
    New variable:
    id = 74, level = 0 is_generic = false, scope = 0
    New variable:
    id = 75, level = 0 is_generic = false, scope = 0
    New former:
    id = 76, level = 0 is_generic = false, scope = 0
    ((structure((Tuple(((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false))))))(level 0)(is_generic false))
    Unify: 72 76
    Unify: 74 66
    Unify: 75 69
    Before exit:
    Current level: 0
    Region 0
    id = 67, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 72, level = 0 is_generic = false, scope = 0
    ((structure((Tuple(((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false))))))(level 0)(is_generic false))
    id = 64, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 72, level = 0 is_generic = false, scope = 0
    ((structure((Tuple(((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false))))))(level 0)(is_generic false))
    id = 75, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 62, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Arrow((structure((Tuple(((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false))))))(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))((structure((Arrow((structure())(level 0)(is_generic false))((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 75, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 74, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 73, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Tuple(((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false))))))(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 74, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 70, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 67, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 73, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Tuple(((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false))))))(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Scope Array order:
    73,67,70,74,73,74,75,62,75,72,64,72,67
    Array order:
    73,67,70,74,73,74,75,62,75,72,64,72,67
    After exit:
    Current level: -1
    Region 0
    Variables: α70,α74,α75
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Arrow
             └──Type expr: Tuple
                └──Type expr: Variable: α74
                └──Type expr: Variable: α75
             └──Type expr: Variable: α70
          └──Type expr: Arrow
             └──Type expr: Variable: α74
             └──Type expr: Arrow
                └──Type expr: Variable: α75
                └──Type expr: Variable: α70
       └──Desc: Function
          └──Pattern:
             └──Type expr: Arrow
                └──Type expr: Tuple
                   └──Type expr: Variable: α74
                   └──Type expr: Variable: α75
                └──Type expr: Variable: α70
             └──Desc: Variable: f
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Variable: α74
                └──Type expr: Arrow
                   └──Type expr: Variable: α75
                   └──Type expr: Variable: α70
             └──Desc: Function
                └──Pattern:
                   └──Type expr: Variable: α74
                   └──Desc: Variable: x
                └──Expression:
                   └──Type expr: Arrow
                      └──Type expr: Variable: α75
                      └──Type expr: Variable: α70
                   └──Desc: Function
                      └──Pattern:
                         └──Type expr: Variable: α75
                         └──Desc: Variable: y
                      └──Expression:
                         └──Type expr: Variable: α70
                         └──Desc: Application
                            └──Expression:
                               └──Type expr: Arrow
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: α74
                                     └──Type expr: Variable: α75
                                  └──Type expr: Variable: α70
                               └──Desc: Variable
                                  └──Variable: f
                            └──Expression:
                               └──Type expr: Tuple
                                  └──Type expr: Variable: α74
                                  └──Type expr: Variable: α75
                               └──Desc: Tuple
                                  └──Expression:
                                     └──Type expr: Variable: α74
                                     └──Desc: Variable
                                        └──Variable: x
                                  └──Expression:
                                     └──Type expr: Variable: α75
                                     └──Desc: Variable
                                        └──Variable: y |}]

let%expect_test "function - uncurry" =
  let exp =
    (* fun f (x, y) -> f x y *)
    Pexp_fun
      ( Ppat_var "f"
      , Pexp_fun
          ( Ppat_tuple [ Ppat_var "x"; Ppat_var "y" ]
          , Pexp_app (Pexp_app (Pexp_var "f", Pexp_var "x"), Pexp_var "y") ) )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect{|
    New variable:
    id = 77, level = 0 is_generic = false, scope = 0
    New variable:
    id = 78, level = 0 is_generic = false, scope = 0
    New variable:
    id = 79, level = 0 is_generic = false, scope = 0
    New former:
    id = 80, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 77 80
    New variable:
    id = 81, level = 0 is_generic = false, scope = 0
    New variable:
    id = 82, level = 0 is_generic = false, scope = 0
    New variable:
    id = 83, level = 0 is_generic = false, scope = 0
    New variable:
    id = 84, level = 0 is_generic = false, scope = 0
    New former:
    id = 85, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 79 85
    New former:
    id = 86, level = 0 is_generic = false, scope = 0
    ((structure((Tuple(((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false))))))(level 0)(is_generic false))
    Unify: 81 86
    New variable:
    id = 87, level = 0 is_generic = false, scope = 0
    New former:
    id = 88, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    New variable:
    id = 89, level = 0 is_generic = false, scope = 0
    New former:
    id = 90, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 90 78
    Unify: 89 84
    Unify: 87 83
    Before exit:
    Current level: 0
    Region 0
    id = 81, level = 0 is_generic = false, scope = 0
    ((structure((Tuple(((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false))))))(level 0)(is_generic false))
    id = 88, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 87, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 89, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 77, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Arrow((structure())(level 0)(is_generic false))((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))((structure((Arrow((structure((Tuple(((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false))))))(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 87, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 79, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Tuple(((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false))))))(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 81, level = 0 is_generic = false, scope = 0
    ((structure((Tuple(((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false))))))(level 0)(is_generic false))
    id = 90, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 90, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 89, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 82, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    Scope Array order:
    82,89,90,90,81,79,87,77,89,87,88,81
    Array order:
    82,89,90,90,81,79,87,77,89,87,88,81
    After exit:
    Current level: -1
    Region 0
    Variables: α82,α89,α87
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Arrow
             └──Type expr: Variable: α89
             └──Type expr: Arrow
                └──Type expr: Variable: α87
                └──Type expr: Variable: α82
          └──Type expr: Arrow
             └──Type expr: Tuple
                └──Type expr: Variable: α89
                └──Type expr: Variable: α87
             └──Type expr: Variable: α82
       └──Desc: Function
          └──Pattern:
             └──Type expr: Arrow
                └──Type expr: Variable: α89
                └──Type expr: Arrow
                   └──Type expr: Variable: α87
                   └──Type expr: Variable: α82
             └──Desc: Variable: f
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Tuple
                   └──Type expr: Variable: α89
                   └──Type expr: Variable: α87
                └──Type expr: Variable: α82
             └──Desc: Function
                └──Pattern:
                   └──Type expr: Tuple
                      └──Type expr: Variable: α89
                      └──Type expr: Variable: α87
                   └──Desc: Tuple
                      └──Pattern:
                         └──Type expr: Variable: α89
                         └──Desc: Variable: x
                      └──Pattern:
                         └──Type expr: Variable: α87
                         └──Desc: Variable: y
                └──Expression:
                   └──Type expr: Variable: α82
                   └──Desc: Application
                      └──Expression:
                         └──Type expr: Arrow
                            └──Type expr: Variable: α87
                            └──Type expr: Variable: α82
                         └──Desc: Application
                            └──Expression:
                               └──Type expr: Arrow
                                  └──Type expr: Variable: α89
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: α87
                                     └──Type expr: Variable: α82
                               └──Desc: Variable
                                  └──Variable: f
                            └──Expression:
                               └──Type expr: Variable: α89
                               └──Desc: Variable
                                  └──Variable: x
                      └──Expression:
                         └──Type expr: Variable: α87
                         └──Desc: Variable
                            └──Variable: y |}]

let%expect_test "function - compose" =
  let exp =
    (* fun f g -> fun x -> f (g x) *)
    Pexp_fun
      ( Ppat_var "f"
      , Pexp_fun
          ( Ppat_var "g"
          , Pexp_fun
              ( Ppat_var "x"
              , Pexp_app (Pexp_var "f", Pexp_app (Pexp_var "g", Pexp_var "x"))
              ) ) )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect{|
    New variable:
    id = 91, level = 0 is_generic = false, scope = 0
    New variable:
    id = 92, level = 0 is_generic = false, scope = 0
    New variable:
    id = 93, level = 0 is_generic = false, scope = 0
    New former:
    id = 94, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 91 94
    New variable:
    id = 95, level = 0 is_generic = false, scope = 0
    New variable:
    id = 96, level = 0 is_generic = false, scope = 0
    New former:
    id = 97, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 93 97
    New variable:
    id = 98, level = 0 is_generic = false, scope = 0
    New variable:
    id = 99, level = 0 is_generic = false, scope = 0
    New former:
    id = 100, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 96 100
    New variable:
    id = 101, level = 0 is_generic = false, scope = 0
    New former:
    id = 102, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 102 92
    New variable:
    id = 103, level = 0 is_generic = false, scope = 0
    New former:
    id = 104, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 104 95
    Unify: 103 98
    Before exit:
    Current level: 0
    Region 0
    id = 93, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 96, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 99, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 102, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 103, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 101, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 91, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))((structure((Arrow((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 103, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 104, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 102, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 96, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 104, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Scope Array order:
    104,96,102,104,103,91,101,103,102,99,96,93
    Array order:
    104,96,102,104,103,91,101,103,102,99,96,93
    After exit:
    Current level: -1
    Region 0
    Variables: α101,α103,α99
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Arrow
             └──Type expr: Variable: α101
             └──Type expr: Variable: α99
          └──Type expr: Arrow
             └──Type expr: Arrow
                └──Type expr: Variable: α103
                └──Type expr: Variable: α101
             └──Type expr: Arrow
                └──Type expr: Variable: α103
                └──Type expr: Variable: α99
       └──Desc: Function
          └──Pattern:
             └──Type expr: Arrow
                └──Type expr: Variable: α101
                └──Type expr: Variable: α99
             └──Desc: Variable: f
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Arrow
                   └──Type expr: Variable: α103
                   └──Type expr: Variable: α101
                └──Type expr: Arrow
                   └──Type expr: Variable: α103
                   └──Type expr: Variable: α99
             └──Desc: Function
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: α103
                      └──Type expr: Variable: α101
                   └──Desc: Variable: g
                └──Expression:
                   └──Type expr: Arrow
                      └──Type expr: Variable: α103
                      └──Type expr: Variable: α99
                   └──Desc: Function
                      └──Pattern:
                         └──Type expr: Variable: α103
                         └──Desc: Variable: x
                      └──Expression:
                         └──Type expr: Variable: α99
                         └──Desc: Application
                            └──Expression:
                               └──Type expr: Arrow
                                  └──Type expr: Variable: α101
                                  └──Type expr: Variable: α99
                               └──Desc: Variable
                                  └──Variable: f
                            └──Expression:
                               └──Type expr: Variable: α101
                               └──Desc: Application
                                  └──Expression:
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: α103
                                        └──Type expr: Variable: α101
                                     └──Desc: Variable
                                        └──Variable: g
                                  └──Expression:
                                     └──Type expr: Variable: α103
                                     └──Desc: Variable
                                        └──Variable: x |}]

let%expect_test "function - fst" =
  let exp =
    (* fun (x, y) -> x *)
    Pexp_fun (Ppat_tuple [ Ppat_var "x"; Ppat_var "y" ], Pexp_var "x")
  in
  print_infer_result ~env:Env.empty exp;
  [%expect{|
    New variable:
    id = 105, level = 0 is_generic = false, scope = 0
    New variable:
    id = 106, level = 0 is_generic = false, scope = 0
    New variable:
    id = 107, level = 0 is_generic = false, scope = 0
    New variable:
    id = 108, level = 0 is_generic = false, scope = 0
    New variable:
    id = 109, level = 0 is_generic = false, scope = 0
    New former:
    id = 110, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 105 110
    New former:
    id = 111, level = 0 is_generic = false, scope = 0
    ((structure((Tuple(((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false))))))(level 0)(is_generic false))
    Unify: 106 111
    Unify: 107 109
    Before exit:
    Current level: 0
    Region 0
    id = 105, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Tuple(((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false))))))(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 107, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 106, level = 0 is_generic = false, scope = 0
    ((structure((Tuple(((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false))))))(level 0)(is_generic false))
    id = 106, level = 0 is_generic = false, scope = 0
    ((structure((Tuple(((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false))))))(level 0)(is_generic false))
    id = 107, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 108, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 105, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Tuple(((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false))))))(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Scope Array order:
    105,108,107,106,106,107,105
    Array order:
    105,108,107,106,106,107,105
    After exit:
    Current level: -1
    Region 0
    Variables: α108,α107
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Tuple
             └──Type expr: Variable: α107
             └──Type expr: Variable: α108
          └──Type expr: Variable: α107
       └──Desc: Function
          └──Pattern:
             └──Type expr: Tuple
                └──Type expr: Variable: α107
                └──Type expr: Variable: α108
             └──Desc: Tuple
                └──Pattern:
                   └──Type expr: Variable: α107
                   └──Desc: Variable: x
                └──Pattern:
                   └──Type expr: Variable: α108
                   └──Desc: Variable: y
          └──Expression:
             └──Type expr: Variable: α107
             └──Desc: Variable
                └──Variable: x |}]

let%expect_test "function - snd" =
  let exp =
    (* fun (x, y) -> y *)
    Pexp_fun (Ppat_tuple [ Ppat_var "x"; Ppat_var "y" ], Pexp_var "y")
  in
  print_infer_result ~env:Env.empty exp;
  [%expect{|
    New variable:
    id = 112, level = 0 is_generic = false, scope = 0
    New variable:
    id = 113, level = 0 is_generic = false, scope = 0
    New variable:
    id = 114, level = 0 is_generic = false, scope = 0
    New variable:
    id = 115, level = 0 is_generic = false, scope = 0
    New variable:
    id = 116, level = 0 is_generic = false, scope = 0
    New former:
    id = 117, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 112 117
    New former:
    id = 118, level = 0 is_generic = false, scope = 0
    ((structure((Tuple(((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false))))))(level 0)(is_generic false))
    Unify: 113 118
    Unify: 114 115
    Before exit:
    Current level: 0
    Region 0
    id = 113, level = 0 is_generic = false, scope = 0
    ((structure((Tuple(((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false))))))(level 0)(is_generic false))
    id = 114, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 114, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 113, level = 0 is_generic = false, scope = 0
    ((structure((Tuple(((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false))))))(level 0)(is_generic false))
    id = 112, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Tuple(((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false))))))(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 116, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 112, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Tuple(((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false))))))(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Scope Array order:
    112,116,112,113,114,114,113
    Array order:
    112,116,112,113,114,114,113
    After exit:
    Current level: -1
    Region 0
    Variables: α116,α114
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Tuple
             └──Type expr: Variable: α116
             └──Type expr: Variable: α114
          └──Type expr: Variable: α114
       └──Desc: Function
          └──Pattern:
             └──Type expr: Tuple
                └──Type expr: Variable: α116
                └──Type expr: Variable: α114
             └──Desc: Tuple
                └──Pattern:
                   └──Type expr: Variable: α116
                   └──Desc: Variable: x
                └──Pattern:
                   └──Type expr: Variable: α114
                   └──Desc: Variable: y
          └──Expression:
             └──Type expr: Variable: α114
             └──Desc: Variable
                └──Variable: y |}]

let%expect_test "function - hd" =
  let env = add_list Env.empty in
  let exp =
    (* fun (Cons (x, _)) -> x *)
    Pexp_fun
      ( Ppat_construct ("Cons", Some ([], Ppat_tuple [ Ppat_var "x"; Ppat_any ]))
      , Pexp_var "x" )
  in
  print_infer_result ~env exp;
  [%expect{|
    New variable:
    id = 119, level = 0 is_generic = false, scope = 0
    New variable:
    id = 120, level = 0 is_generic = false, scope = 0
    New variable:
    id = 121, level = 0 is_generic = false, scope = 0
    New variable:
    id = 122, level = 0 is_generic = false, scope = 0
    New former:
    id = 123, level = 0 is_generic = false, scope = 0
    ((structure((Constr(((structure())(level 0)(is_generic false)))list)))(level 0)(is_generic false))
    New former:
    id = 124, level = 0 is_generic = false, scope = 0
    ((structure((Tuple(((structure())(level 0)(is_generic false))((structure((Constr(((structure())(level 0)(is_generic false)))list)))(level 0)(is_generic false))))))(level 0)(is_generic false))
    New former:
    id = 125, level = 0 is_generic = false, scope = 0
    ((structure((Constr(((structure())(level 0)(is_generic false)))list)))(level 0)(is_generic false))
    New variable:
    id = 126, level = 0 is_generic = false, scope = 0
    New variable:
    id = 127, level = 0 is_generic = false, scope = 0
    New former:
    id = 128, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 119 128
    Unify: 120 125
    New former:
    id = 129, level = 0 is_generic = false, scope = 0
    ((structure((Tuple(((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false))))))(level 0)(is_generic false))
    Unify: 124 129
    Unify: 121 122
    Before exit:
    Current level: 0
    Region 0
    id = 120, level = 0 is_generic = false, scope = 0
    ((structure((Constr(((structure())(level 0)(is_generic false)))list)))(level 0)(is_generic false))
    id = 119, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr(((structure())(level 0)(is_generic false)))list)))(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 121, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 123, level = 0 is_generic = false, scope = 0
    ((structure((Constr(((structure())(level 0)(is_generic false)))list)))(level 0)(is_generic false))
    id = 123, level = 0 is_generic = false, scope = 0
    ((structure((Constr(((structure())(level 0)(is_generic false)))list)))(level 0)(is_generic false))
    id = 120, level = 0 is_generic = false, scope = 0
    ((structure((Constr(((structure())(level 0)(is_generic false)))list)))(level 0)(is_generic false))
    id = 121, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 119, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr(((structure())(level 0)(is_generic false)))list)))(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 124, level = 0 is_generic = false, scope = 0
    ((structure((Tuple(((structure())(level 0)(is_generic false))((structure((Constr(((structure())(level 0)(is_generic false)))list)))(level 0)(is_generic false))))))(level 0)(is_generic false))
    id = 124, level = 0 is_generic = false, scope = 0
    ((structure((Tuple(((structure())(level 0)(is_generic false))((structure((Constr(((structure())(level 0)(is_generic false)))list)))(level 0)(is_generic false))))))(level 0)(is_generic false))
    id = 121, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    Scope Array order:
    121,124,124,119,121,120,123,123,121,119,120
    Array order:
    121,124,124,119,121,120,123,123,121,119,120
    After exit:
    Current level: -1
    Region 0
    Variables: α121
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Constructor: list
             └──Type expr: Variable: α121
          └──Type expr: Variable: α121
       └──Desc: Function
          └──Pattern:
             └──Type expr: Constructor: list
                └──Type expr: Variable: α121
             └──Desc: Construct
                └──Constructor description:
                   └──Name: Cons
                   └──Constructor argument type:
                      └──Type expr: Tuple
                         └──Type expr: Variable: α121
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: α121
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: α121
                └──Pattern:
                   └──Type expr: Tuple
                      └──Type expr: Variable: α121
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: α121
                   └──Desc: Tuple
                      └──Pattern:
                         └──Type expr: Variable: α121
                         └──Desc: Variable: x
                      └──Pattern:
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: α121
                         └──Desc: Any
          └──Expression:
             └──Type expr: Variable: α121
             └──Desc: Variable
                └──Variable: x |}]

let%expect_test "annotation - identity" =
  let exp =
    (* exists 'a -> fun (x : 'a) -> x *)
    Pexp_exists
      ( [ "a" ]
      , Pexp_fun (Ppat_constraint (Ppat_var "x", Ptyp_var "a"), Pexp_var "x") )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect{|
    New variable:
    id = 130, level = 0 is_generic = false, scope = 0
    New variable:
    id = 131, level = 0 is_generic = false, scope = 0
    New variable:
    id = 132, level = 0 is_generic = false, scope = 0
    New variable:
    id = 133, level = 0 is_generic = false, scope = 0
    New former:
    id = 134, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 130 134
    Unify: 132 131
    Unify: 133 132
    Before exit:
    Current level: 0
    Region 0
    id = 133, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 130, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 130, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 133, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 133, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    Scope Array order:
    133,133,130,130,133
    Array order:
    133,133,130,130,133
    After exit:
    Current level: -1
    Region 0
    Variables: α133
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Variable: α133
          └──Type expr: Variable: α133
       └──Desc: Function
          └──Pattern:
             └──Type expr: Variable: α133
             └──Desc: Variable: x
          └──Expression:
             └──Type expr: Variable: α133
             └──Desc: Variable
                └──Variable: x |}]

let%expect_test "annotation - identity" =
  let exp =
    (* forall 'a -> fun (x : 'a) -> x *)
    Pexp_forall
      ( [ "a" ]
      , Pexp_fun (Ppat_constraint (Ppat_var "x", Ptyp_var "a"), Pexp_var "x") )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect{|
    New variable:
    id = 135, level = 0 is_generic = false, scope = 0
    New variable:
    id = 136, level = 1 is_generic = false, scope = 0
    Solver: bind_rigid
    New variable:
    id = 137, level = 1 is_generic = false, scope = 0
    New variable:
    id = 138, level = 1 is_generic = false, scope = 0
    New former:
    id = 139, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 136 139
    New rigid variable: 0
    id = 140, level = 1 is_generic = false, scope = 0
    Unify: 137 140
    New rigid variable: 0
    id = 141, level = 1 is_generic = false, scope = 0
    Unify: 138 141
    Before exit:
    Current level: 1
    Region 0
    id = 135, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    Region 1
    id = 136, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 138, level = 1 is_generic = false, scope = 0
    ((structure())(level 1)(is_generic false))
    id = 137, level = 1 is_generic = false, scope = 0
    ((structure())(level 1)(is_generic false))
    id = 137, level = 1 is_generic = false, scope = 0
    ((structure())(level 1)(is_generic false))
    id = 138, level = 1 is_generic = false, scope = 0
    ((structure())(level 1)(is_generic false))
    Scope Array order:
    138,137,137,138,136
    Array order:
    138,137,137,138,136
    Cannot flexize rigid var, as it is unbound!("Could not flexize rigid type variable when generalizing" (var "\206\1770")) |}]

let%expect_test "annotation - succ" =
  let exp =
    (* exists 'a -> fun (x : 'a) -> x + 1 *)
    Pexp_exists
      ( [ "a" ]
      , Pexp_fun
          ( Ppat_constraint (Ppat_var "x", Ptyp_var "a")
          , Pexp_app
              ( Pexp_app (Pexp_prim Prim_add, Pexp_var "x")
              , Pexp_const (Const_int 1) ) ) )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect{|
    New variable:
    id = 142, level = 0 is_generic = false, scope = 0
    New variable:
    id = 143, level = 0 is_generic = false, scope = 0
    New variable:
    id = 144, level = 0 is_generic = false, scope = 0
    New variable:
    id = 145, level = 0 is_generic = false, scope = 0
    New former:
    id = 146, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 142 146
    Unify: 144 143
    New variable:
    id = 147, level = 0 is_generic = false, scope = 0
    New former:
    id = 148, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    New variable:
    id = 149, level = 0 is_generic = false, scope = 0
    New former:
    id = 150, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    New former:
    id = 151, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    New former:
    id = 152, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    New former:
    id = 153, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    New former:
    id = 154, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    New former:
    id = 155, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 150 155
    Unify: 149 144
    New former:
    id = 156, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    Unify: 147 156
    Before exit:
    Current level: 0
    Region 0
    id = 150, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 147, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 145, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 150, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 147, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 145, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 148, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 149, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 149, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 148, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 142, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 149, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 147, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    Scope Array order:
    147,149,142,148,149,149,148,145,147,150,145,147,150
    Array order:
    147,149,142,148,149,149,148,145,147,150,145,147,150
    After exit:
    Current level: -1
    Region 0
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Constructor: int
          └──Type expr: Constructor: int
       └──Desc: Function
          └──Pattern:
             └──Type expr: Constructor: int
             └──Desc: Variable: x
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
                   └──Desc: Constant: 1 |}]

let%expect_test "annotation - succ" =
  let exp =
    (* exists 'a -> fun (x : 'a) -> x + 1 *)
    Pexp_forall
      ( [ "a" ]
      , Pexp_fun
          ( Ppat_constraint (Ppat_var "x", Ptyp_var "a")
          , Pexp_app
              ( Pexp_app (Pexp_prim Prim_add, Pexp_var "x")
              , Pexp_const (Const_int 1) ) ) )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect{|
    New variable:
    id = 157, level = 0 is_generic = false, scope = 0
    New variable:
    id = 158, level = 1 is_generic = false, scope = 0
    Solver: bind_rigid
    New variable:
    id = 159, level = 1 is_generic = false, scope = 0
    New variable:
    id = 160, level = 1 is_generic = false, scope = 0
    New former:
    id = 161, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 158 161
    New rigid variable: 1
    id = 162, level = 1 is_generic = false, scope = 0
    Unify: 159 162
    New rigid variable: 1
    id = 163, level = 1 is_generic = false, scope = 0
    New variable:
    id = 164, level = 1 is_generic = false, scope = 0
    New former:
    id = 165, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    New variable:
    id = 166, level = 1 is_generic = false, scope = 0
    New former:
    id = 167, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false)))))(level 1)(is_generic false))
    New former:
    id = 168, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    New former:
    id = 169, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    New former:
    id = 170, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    New former:
    id = 171, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    New former:
    id = 172, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 167 172
    Unify: 166 163
    ("Cannot unify types" (type_expr1 (Ttyp_constr (() int)))
     (type_expr2 (Ttyp_var "\206\1771"))) |}]

let%expect_test "let - identity" =
  let exp =
    (* let id x = x in id id () *)
    Pexp_let
      ( Nonrecursive
      , [ { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "id"
          ; pvb_expr = Pexp_fun (Ppat_var "x", Pexp_var "x")
          }
        ]
      , Pexp_app (Pexp_app (Pexp_var "id", Pexp_var "id"), Pexp_const Const_unit)
      )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect{|
    New variable:
    id = 173, level = 0 is_generic = false, scope = 0
    New variable:
    id = 174, level = 1 is_generic = false, scope = 0
    New variable:
    id = 175, level = 1 is_generic = false, scope = 0
    New variable:
    id = 176, level = 1 is_generic = false, scope = 0
    New former:
    id = 177, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 174 177
    Unify: 176 175
    Before exit:
    Current level: 1
    Region 0
    id = 173, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    Region 1
    id = 174, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 176, level = 1 is_generic = false, scope = 0
    ((structure())(level 1)(is_generic false))
    id = 176, level = 1 is_generic = false, scope = 0
    ((structure())(level 1)(is_generic false))
    id = 174, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    Scope Array order:
    174,176,176,174
    Array order:
    174,176,176,174
    After exit:
    Current level: 0
    Region 0
    id = 173, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    Region 1
    New variable:
    id = 178, level = 0 is_generic = false, scope = 0
    New former:
    id = 179, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    New variable:
    id = 180, level = 0 is_generic = false, scope = 0
    New former:
    id = 181, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    New variable:
    id = 182, level = 0 is_generic = false, scope = 0
    New former:
    id = 183, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 181 183
    New variable:
    id = 184, level = 0 is_generic = false, scope = 0
    New former:
    id = 185, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 179 185
    New former:
    id = 186, level = 0 is_generic = false, scope = 0
    ((structure((Constr()unit)))(level 0)(is_generic false))
    Unify: 173 186
    Before exit:
    Current level: 0
    Region 0
    id = 179, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()unit)))(level 0)(is_generic false))((structure((Constr()unit)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 173, level = 0 is_generic = false, scope = 0
    ((structure((Constr()unit)))(level 0)(is_generic false))
    id = 179, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()unit)))(level 0)(is_generic false))((structure((Constr()unit)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 173, level = 0 is_generic = false, scope = 0
    ((structure((Constr()unit)))(level 0)(is_generic false))
    id = 173, level = 0 is_generic = false, scope = 0
    ((structure((Constr()unit)))(level 0)(is_generic false))
    id = 173, level = 0 is_generic = false, scope = 0
    ((structure((Constr()unit)))(level 0)(is_generic false))
    id = 181, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Arrow((structure((Constr()unit)))(level 0)(is_generic false))((structure((Constr()unit)))(level 0)(is_generic false)))))(level 0)(is_generic false))((structure((Arrow((structure((Constr()unit)))(level 0)(is_generic false))((structure((Constr()unit)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    Region 1
    Scope Array order:
    181,173,173,173,179,173,179
    Array order:
    181,173,173,173,179,173,179
    After exit:
    Current level: -1
    Region 0
    Region 1
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Constructor: unit
       └──Desc: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: α176
                      └──Type expr: Variable: α176
                   └──Desc: Variable: id
                └──Abstraction:
                   └──Variables: α176
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: α176
                         └──Type expr: Variable: α176
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: α176
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: α176
                            └──Desc: Variable
                               └──Variable: x
          └──Expression:
             └──Type expr: Constructor: unit
             └──Desc: Application
                └──Expression:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: unit
                      └──Type expr: Constructor: unit
                   └──Desc: Application
                      └──Expression:
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Constructor: unit
                               └──Type expr: Constructor: unit
                            └──Type expr: Arrow
                               └──Type expr: Constructor: unit
                               └──Type expr: Constructor: unit
                         └──Desc: Variable
                            └──Variable: id
                            └──Type expr: Arrow
                               └──Type expr: Constructor: unit
                               └──Type expr: Constructor: unit
                      └──Expression:
                         └──Type expr: Arrow
                            └──Type expr: Constructor: unit
                            └──Type expr: Constructor: unit
                         └──Desc: Variable
                            └──Variable: id
                            └──Type expr: Constructor: unit
                └──Expression:
                   └──Type expr: Constructor: unit
                   └──Desc: Constant: () |}]

(* ('a -> 'a) -> (unit -> 'b) *)
(* 'a -> 'a *)

let%expect_test "let - map" =
  let env = add_list Env.empty in
  let exp =
    (* let rec map f xs = match xs with (Nil -> Nil | Cons (x, xs) -> Cons (f x, map f xs)) in let f x = x + 1 in map f Nil *)
    Pexp_let
      ( Recursive
      , [ { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "map"
          ; pvb_expr =
              Pexp_fun
                ( Ppat_var "f"
                , Pexp_fun
                    ( Ppat_var "xs"
                    , Pexp_match
                        ( Pexp_var "xs"
                        , [ { pc_lhs = Ppat_construct ("Nil", None)
                            ; pc_rhs = Pexp_construct ("Nil", None)
                            }
                          ; { pc_lhs =
                                Ppat_construct
                                  ( "Cons"
                                  , Some
                                      ( []
                                      , Ppat_tuple
                                          [ Ppat_var "x"; Ppat_var "xs" ] ) )
                            ; pc_rhs =
                                Pexp_construct
                                  ( "Cons"
                                  , Some
                                      (Pexp_tuple
                                         [ Pexp_app (Pexp_var "f", Pexp_var "x")
                                         ; Pexp_app
                                             ( Pexp_app
                                                 (Pexp_var "map", Pexp_var "f")
                                             , Pexp_var "xs" )
                                         ]) )
                            }
                          ] ) ) )
          }
        ]
      , Pexp_let
          ( Nonrecursive
          , [ { pvb_forall_vars = []
              ; pvb_pat = Ppat_var "f"
              ; pvb_expr =
                  Pexp_fun
                    ( Ppat_var "x"
                    , Pexp_app
                        ( Pexp_app (Pexp_prim Prim_add, Pexp_var "x")
                        , Pexp_const (Const_int 1) ) )
              }
            ]
          , Pexp_app
              ( Pexp_app (Pexp_var "map", Pexp_var "f")
              , Pexp_construct ("Nil", None) ) ) )
  in
  print_infer_result ~env exp;
  [%expect{|
    New variable:
    id = 187, level = 0 is_generic = false, scope = 0
    New variable:
    id = 188, level = 1 is_generic = false, scope = 0
    New variable:
    id = 189, level = 1 is_generic = false, scope = 0
    New variable:
    id = 190, level = 1 is_generic = false, scope = 0
    New former:
    id = 191, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 188 191
    New variable:
    id = 192, level = 1 is_generic = false, scope = 0
    New variable:
    id = 193, level = 1 is_generic = false, scope = 0
    New former:
    id = 194, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 190 194
    New variable:
    id = 195, level = 1 is_generic = false, scope = 0
    Unify: 195 192
    New variable:
    id = 196, level = 1 is_generic = false, scope = 0
    New former:
    id = 197, level = 1 is_generic = false, scope = 0
    ((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false))
    Unify: 195 197
    New variable:
    id = 198, level = 1 is_generic = false, scope = 0
    New former:
    id = 199, level = 1 is_generic = false, scope = 0
    ((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false))
    Unify: 193 199
    New variable:
    id = 200, level = 1 is_generic = false, scope = 0
    New former:
    id = 201, level = 1 is_generic = false, scope = 0
    ((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false))
    New former:
    id = 202, level = 1 is_generic = false, scope = 0
    ((structure((Tuple(((structure())(level 1)(is_generic false))((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false))))))(level 1)(is_generic false))
    New former:
    id = 203, level = 1 is_generic = false, scope = 0
    ((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false))
    New variable:
    id = 204, level = 1 is_generic = false, scope = 0
    New variable:
    id = 205, level = 1 is_generic = false, scope = 0
    Unify: 195 203
    New former:
    id = 206, level = 1 is_generic = false, scope = 0
    ((structure((Tuple(((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false))))))(level 1)(is_generic false))
    Unify: 202 206
    New variable:
    id = 207, level = 1 is_generic = false, scope = 0
    New former:
    id = 208, level = 1 is_generic = false, scope = 0
    ((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false))
    New former:
    id = 209, level = 1 is_generic = false, scope = 0
    ((structure((Tuple(((structure())(level 1)(is_generic false))((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false))))))(level 1)(is_generic false))
    New former:
    id = 210, level = 1 is_generic = false, scope = 0
    ((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false))
    Unify: 193 210
    New variable:
    id = 211, level = 1 is_generic = false, scope = 0
    New variable:
    id = 212, level = 1 is_generic = false, scope = 0
    New former:
    id = 213, level = 1 is_generic = false, scope = 0
    ((structure((Tuple(((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false))))))(level 1)(is_generic false))
    Unify: 209 213
    New variable:
    id = 214, level = 1 is_generic = false, scope = 0
    New former:
    id = 215, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 215 189
    Unify: 214 196
    New variable:
    id = 216, level = 1 is_generic = false, scope = 0
    New former:
    id = 217, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    New variable:
    id = 218, level = 1 is_generic = false, scope = 0
    New former:
    id = 219, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure((Arrow((structure())(level 1)(is_generic false))((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false)))))(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 219 188
    Unify: 218 218
    Unify: 216 201
    Before exit:
    Current level: 1
    Region 0
    id = 187, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    Region 1
    id = 216, level = 1 is_generic = false, scope = 0
    ((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false))
    id = 198, level = 1 is_generic = false, scope = 0
    ((structure())(level 1)(is_generic false))
    id = 216, level = 1 is_generic = false, scope = 0
    ((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false))
    id = 198, level = 1 is_generic = false, scope = 0
    ((structure())(level 1)(is_generic false))
    id = 209, level = 1 is_generic = false, scope = 0
    ((structure((Tuple(((structure())(level 1)(is_generic false))((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false))))))(level 1)(is_generic false))
    id = 216, level = 1 is_generic = false, scope = 0
    ((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false))
    id = 202, level = 1 is_generic = false, scope = 0
    ((structure((Tuple(((structure())(level 1)(is_generic false))((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false))))))(level 1)(is_generic false))
    id = 208, level = 1 is_generic = false, scope = 0
    ((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false))
    id = 214, level = 1 is_generic = false, scope = 0
    ((structure())(level 1)(is_generic false))
    id = 217, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false))((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 198, level = 1 is_generic = false, scope = 0
    ((structure())(level 1)(is_generic false))
    id = 209, level = 1 is_generic = false, scope = 0
    ((structure((Tuple(((structure())(level 1)(is_generic false))((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false))))))(level 1)(is_generic false))
    id = 214, level = 1 is_generic = false, scope = 0
    ((structure())(level 1)(is_generic false))
    id = 217, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false))((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 218, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 208, level = 1 is_generic = false, scope = 0
    ((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false))
    id = 208, level = 1 is_generic = false, scope = 0
    ((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false))
    id = 219, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))((structure((Arrow((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false))((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false)))))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 219, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))((structure((Arrow((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false))((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false)))))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 208, level = 1 is_generic = false, scope = 0
    ((structure((Constr(((structure())(level 1)(is_generic false)))list)))(level 1)(is_generic false))
    id = 218, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 218, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    Scope Array order:
    218,218,208,219,219,208,208,218,217,214,209,198,217,214,208,202,216,209,198,216,198,216
    Array order:
    218,218,208,219,219,208,208,218,217,214,209,198,217,214,208,202,216,209,198,216,198,216
    After exit:
    Current level: 0
    Region 0
    id = 187, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    Region 1
    New variable:
    id = 220, level = 1 is_generic = false, scope = 0
    New variable:
    id = 221, level = 1 is_generic = false, scope = 0
    New variable:
    id = 222, level = 1 is_generic = false, scope = 0
    New former:
    id = 223, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 220 223
    New variable:
    id = 224, level = 1 is_generic = false, scope = 0
    New former:
    id = 225, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    New variable:
    id = 226, level = 1 is_generic = false, scope = 0
    New former:
    id = 227, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false)))))(level 1)(is_generic false))
    New former:
    id = 228, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    New former:
    id = 229, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    New former:
    id = 230, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    New former:
    id = 231, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    New former:
    id = 232, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 227 232
    Unify: 226 221
    New former:
    id = 233, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    Unify: 224 233
    Before exit:
    Current level: 1
    Region 0
    id = 187, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    Region 1
    id = 220, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 225, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 224, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 224, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 226, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 227, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 224, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 225, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 220, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 222, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 226, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 226, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 227, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 222, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    Region 2
    Scope Array order:
    222,227,226,226,222,220,225,224,227,226,224,224,225,220
    Array order:
    222,227,226,226,222,220,225,224,227,226,224,224,225,220
    After exit:
    Current level: 0
    Region 0
    id = 225, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 187, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 224, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 226, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 227, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 220, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 222, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    Region 1
    Region 2
    New variable:
    id = 234, level = 0 is_generic = false, scope = 0
    New former:
    id = 235, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    New variable:
    id = 236, level = 0 is_generic = false, scope = 0
    New former:
    id = 237, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    New variable:
    id = 238, level = 0 is_generic = false, scope = 0
    New variable:
    id = 239, level = 0 is_generic = false, scope = 0
    New former:
    id = 240, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))
    New former:
    id = 241, level = 0 is_generic = false, scope = 0
    ((structure((Constr(((structure())(level 0)(is_generic false)))list)))(level 0)(is_generic false))
    New former:
    id = 242, level = 0 is_generic = false, scope = 0
    ((structure((Constr(((structure())(level 0)(is_generic false)))list)))(level 0)(is_generic false))
    New former:
    id = 243, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr(((structure())(level 0)(is_generic false)))list)))(level 0)(is_generic false))((structure((Constr(((structure())(level 0)(is_generic false)))list)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    New former:
    id = 244, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Arrow((structure())(level 0)(is_generic false))((structure())(level 0)(is_generic false)))))(level 0)(is_generic false))((structure((Arrow((structure((Constr(((structure())(level 0)(is_generic false)))list)))(level 0)(is_generic false))((structure((Constr(((structure())(level 0)(is_generic false)))list)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 237 244
    Unify: 236 220
    New variable:
    id = 245, level = 0 is_generic = false, scope = 0
    New former:
    id = 246, level = 0 is_generic = false, scope = 0
    ((structure((Constr(((structure())(level 0)(is_generic false)))list)))(level 0)(is_generic false))
    Unify: 234 246
    Before exit:
    Current level: 0
    Region 0
    id = 235, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr(((structure((Constr()int)))(level 0)(is_generic false)))list)))(level 0)(is_generic false))((structure((Constr(((structure((Constr()int)))(level 0)(is_generic false)))list)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 238, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 234, level = 0 is_generic = false, scope = 0
    ((structure((Constr(((structure((Constr()int)))(level 0)(is_generic false)))list)))(level 0)(is_generic false))
    id = 234, level = 0 is_generic = false, scope = 0
    ((structure((Constr(((structure((Constr()int)))(level 0)(is_generic false)))list)))(level 0)(is_generic false))
    id = 236, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 225, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 224, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 235, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr(((structure((Constr()int)))(level 0)(is_generic false)))list)))(level 0)(is_generic false))((structure((Constr(((structure((Constr()int)))(level 0)(is_generic false)))list)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 237, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))((structure((Arrow((structure((Constr(((structure((Constr()int)))(level 0)(is_generic false)))list)))(level 0)(is_generic false))((structure((Constr(((structure((Constr()int)))(level 0)(is_generic false)))list)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 238, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 187, level = 0 is_generic = false, scope = 0
    ((structure((Constr(((structure((Constr()int)))(level 0)(is_generic false)))list)))(level 0)(is_generic false))
    id = 237, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))((structure((Arrow((structure((Constr(((structure((Constr()int)))(level 0)(is_generic false)))list)))(level 0)(is_generic false))((structure((Constr(((structure((Constr()int)))(level 0)(is_generic false)))list)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 187, level = 0 is_generic = false, scope = 0
    ((structure((Constr(((structure((Constr()int)))(level 0)(is_generic false)))list)))(level 0)(is_generic false))
    id = 238, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 236, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 236, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 227, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 239, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 234, level = 0 is_generic = false, scope = 0
    ((structure((Constr(((structure((Constr()int)))(level 0)(is_generic false)))list)))(level 0)(is_generic false))
    id = 239, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    Region 1
    Region 2
    Scope Array order:
    239,234,239,227,236,236,238,187,237,187,238,237,235,224,225,236,234,234,238,235
    Array order:
    239,234,239,227,236,236,238,187,237,187,238,237,235,224,225,236,234,234,238,235
    After exit:
    Current level: -1
    Region 0
    Region 1
    Region 2
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Constructor: list
          └──Type expr: Constructor: int
       └──Desc: Let rec
          └──Value bindings:
             └──Value binding:
                └──Variable: map
                └──Abstraction:
                   └──Variables: α198,α214
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: α214
                            └──Type expr: Variable: α198
                         └──Type expr: Arrow
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: α214
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: α198
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Variable: α214
                               └──Type expr: Variable: α198
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: α214
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: α198
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: α214
                                  └──Desc: Variable: xs
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: α198
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Variable: α214
                                        └──Desc: Variable
                                           └──Variable: xs
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: α214
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: α214
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α214
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: α198
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α198
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: α214
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: α214
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: α214
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α214
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: α214
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α214
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Variable: α214
                                                          └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: α214
                                                          └──Desc: Variable: xs
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: α198
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: α198
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: α198
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α198
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: α198
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α198
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Variable: α198
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: α214
                                                                   └──Type expr: Variable: α198
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Variable: α214
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: α198
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: α214
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: α198
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Variable: α214
                                                                            └──Type expr: Variable: α198
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: α214
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: α198
                                                                      └──Desc: Variable
                                                                         └──Variable: map
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: α214
                                                                         └──Type expr: Variable: α198
                                                                      └──Desc: Variable
                                                                         └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: α214
                                                                └──Desc: Variable
                                                                   └──Variable: xs
          └──Expression:
             └──Type expr: Constructor: list
                └──Type expr: Constructor: int
             └──Desc: Let
                └──Value bindings:
                   └──Value binding:
                      └──Pattern:
                         └──Type expr: Arrow
                            └──Type expr: Constructor: int
                            └──Type expr: Constructor: int
                         └──Desc: Variable: f
                      └──Abstraction:
                         └──Variables:
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable: x
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
                                        └──Desc: Constant: 1
                └──Expression:
                   └──Type expr: Constructor: list
                      └──Type expr: Constructor: int
                   └──Desc: Application
                      └──Expression:
                         └──Type expr: Arrow
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: int
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: int
                         └──Desc: Application
                            └──Expression:
                               └──Type expr: Arrow
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: list
                                        └──Type expr: Constructor: int
                                     └──Type expr: Constructor: list
                                        └──Type expr: Constructor: int
                               └──Desc: Variable
                                  └──Variable: map
                                  └──Type expr: Constructor: int
                                  └──Type expr: Constructor: int
                            └──Expression:
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: int
                                  └──Type expr: Constructor: int
                               └──Desc: Variable
                                  └──Variable: f
                      └──Expression:
                         └──Type expr: Constructor: list
                            └──Type expr: Constructor: int
                         └──Desc: Construct
                            └──Constructor description:
                               └──Name: Nil
                               └──Constructor type:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Constructor: int |}]

let%expect_test "let rec - monomorphic recursion" =
  let env = add_list Env.empty in
  let exp =
    (* let rec id x = x and id_int x = id (x : int) in id_int *)
    Pexp_let
      ( Recursive
      , [ { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "id"
          ; pvb_expr = Pexp_fun (Ppat_var "x", Pexp_var "x")
          }
        ; { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "id_int"
          ; pvb_expr =
              Pexp_fun
                ( Ppat_var "x"
                , Pexp_app
                    ( Pexp_var "id"
                    , Pexp_constraint (Pexp_var "x", Ptyp_constr ([], "int")) )
                )
          }
        ]
      , Pexp_var "id" )
  in
  print_infer_result ~env exp;
  [%expect{|
    New variable:
    id = 247, level = 0 is_generic = false, scope = 0
    New variable:
    id = 248, level = 1 is_generic = false, scope = 0
    New variable:
    id = 249, level = 1 is_generic = false, scope = 0
    New variable:
    id = 250, level = 1 is_generic = false, scope = 0
    New variable:
    id = 251, level = 1 is_generic = false, scope = 0
    New former:
    id = 252, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 248 252
    Unify: 251 250
    New variable:
    id = 253, level = 1 is_generic = false, scope = 0
    New variable:
    id = 254, level = 1 is_generic = false, scope = 0
    New former:
    id = 255, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 249 255
    New variable:
    id = 256, level = 1 is_generic = false, scope = 0
    New former:
    id = 257, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 257 248
    New former:
    id = 258, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    New former:
    id = 259, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    Unify: 254 259
    Unify: 258 253
    Before exit:
    Current level: 1
    Region 0
    id = 247, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    Region 1
    id = 257, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 254, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 254, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 258, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 254, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 254, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 258, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 257, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 249, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    Scope Array order:
    249,257,258,254,254,258,254,254,257
    Array order:
    249,257,258,254,254,258,254,254,257
    After exit:
    Current level: 0
    Region 0
    id = 247, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 254, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 257, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 258, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 249, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    Region 1
    Unify: 247 257
    Before exit:
    Current level: 0
    Region 0
    id = 247, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 254, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 247, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 258, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 249, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    Region 1
    Scope Array order:
    249,258,247,254,247
    Array order:
    249,258,247,254,247
    After exit:
    Current level: -1
    Region 0
    Region 1
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Constructor: int
          └──Type expr: Constructor: int
       └──Desc: Let rec
          └──Value bindings:
             └──Value binding:
                └──Variable: id_int
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Variable
                               └──Variable: x
             └──Value binding:
                └──Variable: id
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: id
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: x
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Constructor: int
                └──Type expr: Constructor: int
             └──Desc: Variable
                └──Variable: id |}]

let%expect_test "let rec - mutual recursion (monomorphic)" =
  let exp =
    (* let rec is_even x = if x = 0 then true else is_odd (x - 1) and is_odd x = if x = 1 then true else is_even (x - 1) in is_even *)
    Pexp_let
      ( Recursive
      , [ { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "is_even"
          ; pvb_expr =
              Pexp_fun
                ( Ppat_var "x"
                , Pexp_ifthenelse
                    ( Pexp_app
                        ( Pexp_app (Pexp_prim Prim_eq, Pexp_var "x")
                        , Pexp_const (Const_int 0) )
                    , Pexp_const (Const_bool true)
                    , Pexp_app
                        ( Pexp_var "is_odd"
                        , Pexp_app
                            ( Pexp_app (Pexp_prim Prim_sub, Pexp_var "x")
                            , Pexp_const (Const_int 1) ) ) ) )
          }
        ; { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "is_odd"
          ; pvb_expr =
              Pexp_fun
                ( Ppat_var "x"
                , Pexp_ifthenelse
                    ( Pexp_app
                        ( Pexp_app (Pexp_prim Prim_eq, Pexp_var "x")
                        , Pexp_const (Const_int 1) )
                    , Pexp_const (Const_bool true)
                    , Pexp_app
                        ( Pexp_var "is_even"
                        , Pexp_app
                            ( Pexp_app (Pexp_prim Prim_sub, Pexp_var "x")
                            , Pexp_const (Const_int 1) ) ) ) )
          }
        ]
      , Pexp_var "is_even" )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect{|
    New variable:
    id = 260, level = 0 is_generic = false, scope = 0
    New variable:
    id = 261, level = 1 is_generic = false, scope = 0
    New variable:
    id = 262, level = 1 is_generic = false, scope = 0
    New variable:
    id = 263, level = 1 is_generic = false, scope = 0
    New variable:
    id = 264, level = 1 is_generic = false, scope = 0
    New former:
    id = 265, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 261 265
    New former:
    id = 266, level = 1 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 1)(is_generic false))
    New variable:
    id = 267, level = 1 is_generic = false, scope = 0
    New former:
    id = 268, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure((Constr()bool)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    New variable:
    id = 269, level = 1 is_generic = false, scope = 0
    New former:
    id = 270, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure((Arrow((structure())(level 1)(is_generic false))((structure((Constr()bool)))(level 1)(is_generic false)))))(level 1)(is_generic false)))))(level 1)(is_generic false))
    New former:
    id = 271, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    New former:
    id = 272, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    New former:
    id = 273, level = 1 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 1)(is_generic false))
    New former:
    id = 274, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()bool)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    New former:
    id = 275, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()bool)))(level 1)(is_generic false)))))(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 270 275
    Unify: 269 263
    New former:
    id = 276, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    Unify: 267 276
    New former:
    id = 277, level = 1 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 1)(is_generic false))
    Unify: 264 277
    New variable:
    id = 278, level = 1 is_generic = false, scope = 0
    New former:
    id = 279, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure((Constr()bool)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 279 262
    New variable:
    id = 280, level = 1 is_generic = false, scope = 0
    New former:
    id = 281, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    New variable:
    id = 282, level = 1 is_generic = false, scope = 0
    New former:
    id = 283, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false)))))(level 1)(is_generic false))
    New former:
    id = 284, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    New former:
    id = 285, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    New former:
    id = 286, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    New former:
    id = 287, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    New former:
    id = 288, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 283 288
    Unify: 282 269
    New former:
    id = 289, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    Unify: 280 289
    New variable:
    id = 290, level = 1 is_generic = false, scope = 0
    New variable:
    id = 291, level = 1 is_generic = false, scope = 0
    New former:
    id = 292, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 279 292
    New former:
    id = 293, level = 1 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 1)(is_generic false))
    New variable:
    id = 294, level = 1 is_generic = false, scope = 0
    New former:
    id = 295, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure((Constr()bool)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    New variable:
    id = 296, level = 1 is_generic = false, scope = 0
    New former:
    id = 297, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure((Arrow((structure())(level 1)(is_generic false))((structure((Constr()bool)))(level 1)(is_generic false)))))(level 1)(is_generic false)))))(level 1)(is_generic false))
    New former:
    id = 298, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    New former:
    id = 299, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    New former:
    id = 300, level = 1 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 1)(is_generic false))
    New former:
    id = 301, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()bool)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    New former:
    id = 302, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()bool)))(level 1)(is_generic false)))))(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 297 302
    Unify: 296 278
    New former:
    id = 303, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    Unify: 294 303
    New former:
    id = 304, level = 1 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 1)(is_generic false))
    Unify: 264 304
    New variable:
    id = 305, level = 1 is_generic = false, scope = 0
    New former:
    id = 306, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure((Constr()bool)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 306 261
    New variable:
    id = 307, level = 1 is_generic = false, scope = 0
    New former:
    id = 308, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    New variable:
    id = 309, level = 1 is_generic = false, scope = 0
    New former:
    id = 310, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure((Arrow((structure())(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false)))))(level 1)(is_generic false))
    New former:
    id = 311, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    New former:
    id = 312, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    New former:
    id = 313, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    New former:
    id = 314, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    New former:
    id = 315, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 310 315
    Unify: 309 296
    New former:
    id = 316, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    Unify: 307 316
    Before exit:
    Current level: 1
    Region 0
    id = 260, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    Region 1
    id = 310, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 297, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()bool)))(level 1)(is_generic false)))))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 307, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 279, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()bool)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 307, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 309, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 294, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 309, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 283, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 306, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()bool)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 306, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()bool)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 305, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 280, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 309, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 294, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 293, level = 1 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 1)(is_generic false))
    id = 309, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 305, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 281, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 267, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 309, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 270, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()bool)))(level 1)(is_generic false)))))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 293, level = 1 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 1)(is_generic false))
    id = 308, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 308, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 266, level = 1 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 1)(is_generic false))
    id = 295, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()bool)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 264, level = 1 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 1)(is_generic false))
    id = 268, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()bool)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 305, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 297, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()bool)))(level 1)(is_generic false)))))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 310, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 295, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 1)(is_generic false))((structure((Constr()bool)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 264, level = 1 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 1)(is_generic false))
    id = 294, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 307, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    Scope Array order:
    307,294,264,295,310,297,305,268,264,295,266,308,308,293,270,309,267,281,305,309,293,294,309,280,305,306,306,283,309,294,309,307,279,307,297,310
    Array order:
    307,294,264,295,310,297,305,268,264,295,266,308,308,293,270,309,267,281,305,309,293,294,309,280,305,306,306,283,309,294,309,307,279,307,297,310
    After exit:
    Current level: 0
    Region 0
    id = 281, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 267, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 297, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()bool)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 279, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()bool)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 307, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 270, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()bool)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 309, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 283, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 306, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()bool)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 308, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 266, level = 0 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 0)(is_generic false))
    id = 295, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()bool)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 264, level = 0 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 0)(is_generic false))
    id = 268, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()bool)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 280, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 310, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 260, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 293, level = 0 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 0)(is_generic false))
    id = 305, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 294, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    Region 1
    Unify: 260 306
    Before exit:
    Current level: 0
    Region 0
    id = 281, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 267, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 297, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()bool)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 279, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()bool)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 307, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 270, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()bool)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 309, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 283, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 260, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()bool)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 308, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 266, level = 0 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 0)(is_generic false))
    id = 295, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()bool)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 264, level = 0 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 0)(is_generic false))
    id = 268, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()bool)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 280, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 310, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 260, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure((Constr()int)))(level 0)(is_generic false))((structure((Constr()bool)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 293, level = 0 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 0)(is_generic false))
    id = 305, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 294, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    Region 1
    Scope Array order:
    294,305,293,260,310,280,268,264,295,266,308,260,283,309,270,307,279,297,267,281
    Array order:
    294,305,293,260,310,280,268,264,295,266,308,260,283,309,270,307,279,297,267,281
    After exit:
    Current level: -1
    Region 0
    Region 1
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Constructor: int
          └──Type expr: Constructor: bool
       └──Desc: Let rec
          └──Value bindings:
             └──Value binding:
                └──Variable: is_odd
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: bool
                            └──Desc: If
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
                                        └──Desc: Constant: 0
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Constant: true
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: bool
                                        └──Desc: Variable
                                           └──Variable: is_odd
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
                                                    └──Desc: Primitive: (-)
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 1
             └──Value binding:
                └──Variable: is_even
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: bool
                            └──Desc: If
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
                                        └──Desc: Constant: 1
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Constant: true
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: bool
                                        └──Desc: Variable
                                           └──Variable: is_even
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
                                                    └──Desc: Primitive: (-)
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 1
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Constructor: int
                └──Type expr: Constructor: bool
             └──Desc: Variable
                └──Variable: is_even |}]

let%expect_test "let rec - mutual recursion (polymorphic)" =
  let exp =
    (* let rec foo x = 1 and bar y = true in foo *)
    Pexp_let
      ( Recursive
      , [ { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "foo"
          ; pvb_expr = Pexp_fun (Ppat_var "x", Pexp_const (Const_int 1))
          }
        ; { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "bar"
          ; pvb_expr = Pexp_fun (Ppat_var "y", Pexp_const (Const_bool true))
          }
        ]
      , Pexp_var "foo" )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect{|
    New variable:
    id = 317, level = 0 is_generic = false, scope = 0
    New variable:
    id = 318, level = 1 is_generic = false, scope = 0
    New variable:
    id = 319, level = 1 is_generic = false, scope = 0
    New variable:
    id = 320, level = 1 is_generic = false, scope = 0
    New variable:
    id = 321, level = 1 is_generic = false, scope = 0
    New former:
    id = 322, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 318 322
    New former:
    id = 323, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    Unify: 321 323
    New variable:
    id = 324, level = 1 is_generic = false, scope = 0
    New variable:
    id = 325, level = 1 is_generic = false, scope = 0
    New former:
    id = 326, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 319 326
    New former:
    id = 327, level = 1 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 1)(is_generic false))
    Unify: 325 327
    Before exit:
    Current level: 1
    Region 0
    id = 317, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    Region 1
    id = 320, level = 1 is_generic = false, scope = 0
    ((structure())(level 1)(is_generic false))
    id = 325, level = 1 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 1)(is_generic false))
    id = 321, level = 1 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 1)(is_generic false))
    id = 324, level = 1 is_generic = false, scope = 0
    ((structure())(level 1)(is_generic false))
    id = 325, level = 1 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 1)(is_generic false))
    id = 319, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure((Constr()bool)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 318, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure((Constr()int)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 319, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure((Constr()bool)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    Scope Array order:
    319,318,319,325,324,321,325,320
    Array order:
    319,318,319,325,324,321,325,320
    After exit:
    Current level: 0
    Region 0
    id = 317, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    id = 321, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 325, level = 0 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 0)(is_generic false))
    Region 1
    New variable:
    id = 328, level = 0 is_generic = false, scope = 0
    New former:
    id = 329, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    Unify: 317 329
    Before exit:
    Current level: 0
    Region 0
    id = 317, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 317, level = 0 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 0)(is_generic false))((structure((Constr()int)))(level 0)(is_generic false)))))(level 0)(is_generic false))
    id = 321, level = 0 is_generic = false, scope = 0
    ((structure((Constr()int)))(level 0)(is_generic false))
    id = 325, level = 0 is_generic = false, scope = 0
    ((structure((Constr()bool)))(level 0)(is_generic false))
    id = 328, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    Region 1
    Scope Array order:
    328,325,321,317,317
    Array order:
    328,325,321,317,317
    After exit:
    Current level: -1
    Region 0
    Region 1
    Variables: α328
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Variable: α328
          └──Type expr: Constructor: int
       └──Desc: Let rec
          └──Value bindings:
             └──Value binding:
                └──Variable: bar
                └──Abstraction:
                   └──Variables: α324
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: α320
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: α320
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Constant: 1
             └──Value binding:
                └──Variable: foo
                └──Abstraction:
                   └──Variables: α320
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: α324
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: α324
                            └──Desc: Variable: y
                         └──Expression:
                            └──Type expr: Constructor: bool
                            └──Desc: Constant: true
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Variable: α328
                └──Type expr: Constructor: int
             └──Desc: Variable
                └──Variable: foo
                └──Type expr: Variable: α328 |}]

let%expect_test "f-pottier elaboration 1" =
  let exp =
    (* let u = (fun f -> ()) (fun x -> x) in u *)
    Pexp_let
      ( Nonrecursive
      , [ { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "u"
          ; pvb_expr =
              Pexp_app
                ( Pexp_fun (Ppat_var "f", Pexp_const Const_unit)
                , Pexp_fun (Ppat_var "x", Pexp_var "x") )
          }
        ]
      , Pexp_var "u" )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect{|
    New variable:
    id = 330, level = 0 is_generic = false, scope = 0
    New variable:
    id = 331, level = 1 is_generic = false, scope = 0
    New variable:
    id = 332, level = 1 is_generic = false, scope = 0
    New former:
    id = 333, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    New variable:
    id = 334, level = 1 is_generic = false, scope = 0
    New variable:
    id = 335, level = 1 is_generic = false, scope = 0
    New former:
    id = 336, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 333 336
    New former:
    id = 337, level = 1 is_generic = false, scope = 0
    ((structure((Constr()unit)))(level 1)(is_generic false))
    Unify: 331 337
    New variable:
    id = 338, level = 1 is_generic = false, scope = 0
    New variable:
    id = 339, level = 1 is_generic = false, scope = 0
    New former:
    id = 340, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    Unify: 332 340
    Unify: 339 338
    Before exit:
    Current level: 1
    Region 0
    id = 330, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    Region 1
    id = 339, level = 1 is_generic = false, scope = 0
    ((structure())(level 1)(is_generic false))
    id = 332, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 339, level = 1 is_generic = false, scope = 0
    ((structure())(level 1)(is_generic false))
    id = 332, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 333, level = 1 is_generic = false, scope = 0
    ((structure((Arrow((structure((Arrow((structure())(level 1)(is_generic false))((structure())(level 1)(is_generic false)))))(level 1)(is_generic false))((structure((Constr()unit)))(level 1)(is_generic false)))))(level 1)(is_generic false))
    id = 331, level = 1 is_generic = false, scope = 0
    ((structure((Constr()unit)))(level 1)(is_generic false))
    Scope Array order:
    331,333,332,339,332,339
    Array order:
    331,333,332,339,332,339
    After exit:
    Current level: 0
    Region 0
    id = 331, level = 0 is_generic = false, scope = 0
    ((structure((Constr()unit)))(level 0)(is_generic false))
    id = 330, level = 0 is_generic = false, scope = 0
    ((structure())(level 0)(is_generic false))
    Region 1
    Unify: 330 331
    Before exit:
    Current level: 0
    Region 0
    id = 330, level = 0 is_generic = false, scope = 0
    ((structure((Constr()unit)))(level 0)(is_generic false))
    id = 330, level = 0 is_generic = false, scope = 0
    ((structure((Constr()unit)))(level 0)(is_generic false))
    Region 1
    Scope Array order:
    330,330
    Array order:
    330,330
    After exit:
    Current level: -1
    Region 0
    Region 1
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Constructor: unit
       └──Desc: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: unit
                   └──Desc: Variable: u
                └──Abstraction:
                   └──Variables: α339
                   └──Expression:
                      └──Type expr: Constructor: unit
                      └──Desc: Application
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: α339
                                  └──Type expr: Variable: α339
                               └──Type expr: Constructor: unit
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: α339
                                     └──Type expr: Variable: α339
                                  └──Desc: Variable: f
                               └──Expression:
                                  └──Type expr: Constructor: unit
                                  └──Desc: Constant: ()
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: α339
                               └──Type expr: Variable: α339
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: α339
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Variable: α339
                                  └──Desc: Variable
                                     └──Variable: x
          └──Expression:
             └──Type expr: Constructor: unit
             └──Desc: Variable
                └──Variable: u |}]

let add_eq env =
  let name = "eq" in
  let params = [ "a"; "b" ] in
  let type_ = Ttyp_constr ([ Ttyp_var "a"; Ttyp_var "b" ], name) in
  Env.add_type_decl
    env
    { type_name = name
    ; type_kind =
        Type_variant
          [ { constructor_name = "Refl"
            ; constructor_alphas = params
            ; constructor_arg = None
            ; constructor_type = type_
            ; constructor_constraints = [ Ttyp_var "a", Ttyp_var "b" ]
            }
          ]
    }


let%expect_test "coerce" =
  (* let coerce = forall a b -> fun eq x -> match (eq : (a, b) eq) with Refl -> (x : a :> b) in () *)
  let env = add_eq Env.empty in
  let exp =
    Pexp_let
      ( Nonrecursive
      , [ { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "coerce"
          ; pvb_expr =
              Pexp_forall
                ( [ "a"; "b" ]
                , Pexp_fun
                    ( Ppat_var "eq"
                    , Pexp_fun
                        ( Ppat_constraint (Ppat_var "x", Ptyp_constr ([ Ptyp_var "a"], "t"))
                        , Pexp_match
                            ( Pexp_constraint
                                ( Pexp_var "eq"
                                , Ptyp_constr
                                    ([ Ptyp_var "a"; Ptyp_var "b" ], "eq") )
                            , [ { pc_lhs = Ppat_construct ("Refl", None)
                                ; pc_rhs =
                                    Pexp_constraint (Pexp_var "x", Ptyp_constr ([ Ptyp_var "b"], "t"))
                                }
                              ] ) ) ) )
          }
        ]
      , Pexp_const Const_unit )
  in
  print_constraint_result ~env exp;
  print_infer_result ~env exp;
  [%expect.unreachable]
[@@expect.uncaught_exn {|
  (* CR expect_test_collector: This test expectation appears to contain a backtrace.
     This is strongly discouraged as backtraces are fragile.
     Please change this test to not include a backtrace. *)

  "Assert_failure src/constraints/solver/structure.ml:113:52"
  Raised at Dromedary_constraints_solver__Structure.Ambivalent.Equations.Ctx.add in file "src/constraints/solver/structure.ml", line 113, characters 52-64
  Called from Dromedary_constraints_solver__Solver.Make.Env.add_equation in file "src/constraints/solver/solver.ml", line 264, characters 10-88
  Called from Stdlib__list.fold_left in file "list.ml", line 121, characters 24-34
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 399, characters 18-53
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 346, characters 21-43
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 342, characters 20-41
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 342, characters 20-41
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 345, characters 21-43
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 342, characters 20-41
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 346, characters 21-43
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 346, characters 21-43
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 342, characters 20-41
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 345, characters 21-43
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 342, characters 20-41
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 346, characters 21-43
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 346, characters 21-43
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 342, characters 20-41
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 345, characters 21-43
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 342, characters 20-41
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 346, characters 21-43
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 346, characters 21-43
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 342, characters 20-41
  Called from Dromedary_constraints_solver__Solver.Make.solve_let_binding in file "src/constraints/solver/solver.ml", line 424, characters 16-37
  Called from Dromedary_constraints_solver__Solver.Make.solve_let_bindings.(fun) in file "src/constraints/solver/solver.ml", line 455, characters 12-53
  Called from Stdlib__list.fold_left in file "list.ml", line 121, characters 24-34
  Called from Dromedary_constraints_solver__Solver.Make.solve_let_bindings in file "src/constraints/solver/solver.ml", line 451, characters 6-281
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 376, characters 10-53
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 342, characters 20-41
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 345, characters 21-43
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 342, characters 20-41
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 346, characters 21-43
  Called from Dromedary_constraints_solver__Solver.Make.solve_let_binding in file "src/constraints/solver/solver.ml", line 424, characters 16-37
  Called from Dromedary_constraints_solver__Solver.Make.solve_let_bindings.(fun) in file "src/constraints/solver/solver.ml", line 455, characters 12-53
  Called from Stdlib__list.fold_left in file "list.ml", line 121, characters 24-34
  Called from Dromedary_constraints_solver__Solver.Make.solve_let_bindings in file "src/constraints/solver/solver.ml", line 451, characters 6-281
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 376, characters 10-53
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 342, characters 20-41
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 345, characters 21-43
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 342, characters 20-41
  Called from Dromedary_constraints_solver__Solver.Make.solve_let_binding in file "src/constraints/solver/solver.ml", line 424, characters 16-37
  Called from Dromedary_constraints_solver__Solver.Make.solve_let_bindings.(fun) in file "src/constraints/solver/solver.ml", line 455, characters 12-53
  Called from Stdlib__list.fold_left in file "list.ml", line 121, characters 24-34
  Called from Dromedary_constraints_solver__Solver.Make.solve_let_bindings in file "src/constraints/solver/solver.ml", line 451, characters 6-281
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 376, characters 10-53
  Called from Dromedary_constraints_solver__Solver.Make.solve.(fun) in file "src/constraints/solver/solver.ml", line 342, characters 20-41
  Called from Dromedary_constraints_solver__Solver.Make.solve in file "src/constraints/solver/solver.ml", line 649, characters 24-73
  Called from Typing__Infer.infer.(fun) in file "src/typing/infer.ml", line 1006, characters 2-11
  Called from Test_typing__Test_infer.print_infer_result in file "test/typing/test_infer.ml", line 18, characters 13-33
  Called from Test_typing__Test_infer.(fun) in file "test/typing/test_infer.ml", line 2627, characters 2-29
  Called from Expect_test_collector.Make.Instance.exec in file "collector/expect_test_collector.ml", line 244, characters 12-19

  Trailing output
  ---------------
  ((Exist ((327 ())))
   (Map
    ((Conj
      (Map
       ((Let
         (((Let_binding ()) ((328 ())) ((coerce 328))
           ((Conj (Map ((Conj (Map True)) (Decode 328))))
            (Map
             ((Conj
               (Map
                ((Let
                  (((Let_binding (329 330)) ((331 ()))
                    ((@dromedary.internal.pexp_forall 331))
                    ((Exist ((332 ()) (333 ())))
                     (Map
                      ((Conj
                        ((Exist ((346 ((Arrow 332 333))))) ((Eq 331) 346)))
                       ((Conj (Map ((Conj (Map True)) (Decode 332))))
                        ((Def ((eq 332)))
                         (Map
                          ((Conj
                            ((Exist
                              ((334 ()) (335 ()) (336 ((Constr (329) t)))))
                             (Map
                              ((Conj
                                ((Exist ((345 ((Arrow 334 335)))))
                                 ((Eq 333) 345)))
                               ((Conj
                                 (Map
                                  ((Conj
                                    (Map ((Conj ((Eq 334) 336)) (Map True))))
                                   (Decode 334))))
                                ((Def ((x 336)))
                                 (Map
                                  ((Conj
                                    ((Exist ((337 ())))
                                     (Map
                                      ((Conj
                                        (Map
                                         ((Conj
                                           ((Exist
                                             ((338 ((Constr (329 330) eq)))
                                              (339 ((Constr (329 330) eq)))))
                                            (Map
                                             ((Conj ((Eq 337) 339))
                                              (Map ((Instance eq) 338))))))
                                          (Decode 337))))
                                       ((Conj (Decode 337))
                                        (Map
                                         ((Conj
                                           (Map
                                            ((Exist
                                              ((340 ()) (341 ())
                                               (342 ((Constr (340 341) eq)))))
                                             (Map
                                              ((Conj
                                                (Map
                                                 ((Conj
                                                   (Map
                                                    ((Conj
                                                      (Map
                                                       ((Conj ((Eq 337) 342))
                                                        (Map
                                                         ((Conj (Decode 337))
                                                          (Map True))))))
                                                     (Map True))))
                                                  (Decode 337))))
                                               ((Implication
                                                 (((Var 340) (Var 341))))
                                                ((Def ())
                                                 (Map
                                                  ((Conj
                                                    ((Exist
                                                      ((343 ((Constr (330) t)))
                                                       (344 ((Constr (330) t)))))
                                                     (Map
                                                      ((Conj ((Eq 335) 344))
                                                       (Map ((Instance x) 343))))))
                                                   (Decode 335))))))))))
                                          (Map True))))))))
                                   (Decode 335)))))))))
                           (Decode 333)))))))))))
                 ((Instance @dromedary.internal.pexp_forall) 328))))
              (Decode 328)))))))
        (Map
         ((Conj (Map ((Exist ((347 ((Constr () unit))))) ((Eq 327) 347))))
          (Decode 327))))))
     (Decode 327))))
  New variable:
  id = 341, level = 0 is_generic = false, scope = 0
  New variable:
  id = 342, level = 1 is_generic = false, scope = 0
  New variable:
  id = 343, level = 2 is_generic = false, scope = 0
  Solver: bind_rigid
  Solver: bind_rigid
  New variable:
  id = 344, level = 2 is_generic = false, scope = 0
  New variable:
  id = 345, level = 2 is_generic = false, scope = 0
  New former:
  id = 346, level = 2 is_generic = false, scope = 0
  ((structure((Arrow((structure())(level 2)(is_generic false))((structure())(level 2)(is_generic false)))))(level 2)(is_generic false))
  Unify: 343 346
  New variable:
  id = 347, level = 2 is_generic = false, scope = 0
  New variable:
  id = 348, level = 2 is_generic = false, scope = 0
  New rigid variable: 2
  id = 349, level = 2 is_generic = false, scope = 0
  New former:
  id = 350, level = 2 is_generic = false, scope = 0
  ((structure((Constr(((structure())(level 2)(is_generic false)))t)))(level 2)(is_generic false))
  New former:
  id = 351, level = 2 is_generic = false, scope = 0
  ((structure((Arrow((structure())(level 2)(is_generic false))((structure())(level 2)(is_generic false)))))(level 2)(is_generic false))
  Unify: 345 351
  Unify: 347 350
  New variable:
  id = 352, level = 2 is_generic = false, scope = 0
  New rigid variable: 2
  id = 353, level = 2 is_generic = false, scope = 0
  New rigid variable: 3
  id = 354, level = 2 is_generic = false, scope = 0
  New former:
  id = 355, level = 2 is_generic = false, scope = 0
  ((structure((Constr(((structure())(level 2)(is_generic false))((structure())(level 2)(is_generic false)))eq)))(level 2)(is_generic false))
  New rigid variable: 2
  id = 356, level = 2 is_generic = false, scope = 0
  New rigid variable: 3
  id = 357, level = 2 is_generic = false, scope = 0
  New former:
  id = 358, level = 2 is_generic = false, scope = 0
  ((structure((Constr(((structure())(level 2)(is_generic false))((structure())(level 2)(is_generic false)))eq)))(level 2)(is_generic false))
  Unify: 352 358
  Unify: 355 344
  New variable:
  id = 359, level = 2 is_generic = false, scope = 0
  New variable:
  id = 360, level = 2 is_generic = false, scope = 0
  New former:
  id = 361, level = 2 is_generic = false, scope = 0
  ((structure((Constr(((structure())(level 2)(is_generic false))((structure())(level 2)(is_generic false)))eq)))(level 2)(is_generic false))
  Unify: 352 361 |}]

(* 
let%expect_test "abbrev - morel" =
  let abbrev_ctx =
    let open Types.Algebra.Type_former in
    let abbrev_k =
      let a = Abbreviations.Type.make_var () in
      let pair = Tuple [ a; a ] in
      Abbreviations.Abbreviation.(
        make
          ~former:(Constr ([], "K"))
          ~rank:1
          ~decomposable_positions:[ 0 ]
          ~productivity:(Productive pair)
          ~type_:([ a ], pair))
    in
    let abbrev_f =
      let a = Abbreviations.Type.make_var () in
      let arr = Arrow (a, a) in
      Abbreviations.Abbreviation.(
        make
          ~former:(Constr ([], "F"))
          ~rank:1
          ~productivity:(Productive arr)
          ~decomposable_positions:[ 0 ]
          ~type_:([ a ], arr))
    in
    let abbrev_g =
      let a = Abbreviations.Type.make_var () in
      let k = Abbreviations.Type.make_former (Constr ([ a ], "K")) in
      let f = Constr ([ k ], "F") in
      Abbreviations.Abbreviation.(
        make
          ~former:(Constr ([], "G"))
          ~rank:2
          ~decomposable_positions:[ 0 ]
          ~productivity:(Productive (Arrow (k, k)))
          ~type_:([ a ], f))
    in
    Abbreviations.Ctx.empty
    |> Abbreviations.Ctx.add ~abbrev:abbrev_k
    |> Abbreviations.Ctx.add ~abbrev:abbrev_f
    |> Abbreviations.Ctx.add ~abbrev:abbrev_g
  in
  let exp =
    Pexp_let
      ( Nonrecursive
      , [ { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "f"
          ; pvb_expr =
              Pexp_constraint
                ( Pexp_fun (Ppat_var "x", Pexp_var "x")
                , Ptyp_constr ([ Ptyp_constr ([], "int") ], "G") )
          }
        ]
      , Pexp_exists
          ( [ "a" ]
          , Pexp_fun
              ( Ppat_constraint
                  (Ppat_var "x", Ptyp_constr ([ Ptyp_var "a" ], "K"))
              , Pexp_app (Pexp_var "f", Pexp_var "x") ) ) )
  in
  print_infer_result ~abbrev_ctx ~env:Env.empty exp;
  [%expect{|
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Constructor: K
             └──Type expr: Constructor: int
          └──Type expr: Constructor: K
             └──Type expr: Constructor: int
       └──Desc: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: K
                         └──Type expr: Constructor: int
                      └──Type expr: Constructor: K
                         └──Type expr: Constructor: int
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: K
                            └──Type expr: Constructor: int
                         └──Type expr: Constructor: K
                            └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: K
                               └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: K
                               └──Type expr: Constructor: int
                            └──Desc: Variable
                               └──Variable: x
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Constructor: K
                   └──Type expr: Constructor: int
                └──Type expr: Constructor: K
                   └──Type expr: Constructor: int
             └──Desc: Function
                └──Pattern:
                   └──Type expr: Constructor: K
                      └──Type expr: Constructor: int
                   └──Desc: Variable: x
                └──Expression:
                   └──Type expr: Constructor: K
                      └──Type expr: Constructor: int
                   └──Desc: Application
                      └──Expression:
                         └──Type expr: Arrow
                            └──Type expr: Constructor: K
                               └──Type expr: Constructor: int
                            └──Type expr: Constructor: K
                               └──Type expr: Constructor: int
                         └──Desc: Variable
                            └──Variable: f
                      └──Expression:
                         └──Type expr: Constructor: K
                            └──Type expr: Constructor: int
                         └──Desc: Variable
                            └──Variable: x |}] *)