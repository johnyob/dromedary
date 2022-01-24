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


let print_solve_result cst =
  Constraint.sexp_of_t cst |> Sexp.to_string_hum |> print_endline;
  match Infer.solve cst with
  | Ok _ -> Format.fprintf Format.std_formatter "Constraint is true.\n"
  | Error err -> Sexp.to_string_hum err |> print_endline


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
  [%expect
    {|
    New variable:
    id = 0, level = 0 is_generic = false, scope = 0
    New former:
    id = 1, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    Unify: 0 1
    Before exit:
    Current level: 0
    Region 0
    id = 0, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 0, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
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
  [%expect
    {|
    New variable:
    id = 2, level = 0 is_generic = false, scope = 0
    New former:
    id = 3, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false))
    Unify: 2 3
    Before exit:
    Current level: 0
    Region 0
    id = 2, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false))
    id = 2, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false))
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
  [%expect
    {|
    New variable:
    id = 4, level = 0 is_generic = false, scope = 0
    New former:
    id = 5, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()unit)))(scope 0)))(level 0)(is_generic false))
    Unify: 4 5
    Before exit:
    Current level: 0
    Region 0
    id = 4, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()unit)))(scope 0)))(level 0)(is_generic false))
    id = 4, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()unit)))(scope 0)))(level 0)(is_generic false))
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
  [%expect
    {|
    New variable:
    id = 6, level = 0 is_generic = false, scope = 0
    New variable:
    id = 7, level = 0 is_generic = false, scope = 0
    New former:
    id = 8, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New variable:
    id = 9, level = 0 is_generic = false, scope = 0
    New former:
    id = 10, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 11, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 12, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 13, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 14, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 15, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 10 15
    New variable:
    id = 16, level = 0 is_generic = false, scope = 0
    New former:
    id = 17, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New variable:
    id = 18, level = 0 is_generic = false, scope = 0
    New former:
    id = 19, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 20, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 21, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 22, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 23, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 24, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 19 24
    New former:
    id = 25, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    Unify: 18 25
    New variable:
    id = 26, level = 0 is_generic = false, scope = 0
    New former:
    id = 27, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New variable:
    id = 28, level = 0 is_generic = false, scope = 0
    New former:
    id = 29, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 30, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 31, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 32, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 33, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 34, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 29 34
    New variable:
    id = 35, level = 0 is_generic = false, scope = 0
    New former:
    id = 36, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New variable:
    id = 37, level = 0 is_generic = false, scope = 0
    New former:
    id = 38, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 39, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 40, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 41, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 42, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 43, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 38 43
    New former:
    id = 44, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    Unify: 37 44
    New former:
    id = 45, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    Unify: 35 45
    New variable:
    id = 46, level = 0 is_generic = false, scope = 0
    New former:
    id = 47, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New variable:
    id = 48, level = 0 is_generic = false, scope = 0
    New former:
    id = 49, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 50, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 51, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 52, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 53, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 54, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 49 54
    New former:
    id = 55, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    Unify: 48 55
    New former:
    id = 56, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    Unify: 46 56
    New former:
    id = 57, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    Unify: 7 57
    Before exit:
    Current level: 0
    Region 0
    id = 38, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 29, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 35, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 46, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 7, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 37, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 46, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 9, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 10, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 26, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 36, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 28, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 7, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 36, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 37, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 16, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 37, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 47, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 28, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 47, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 35, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 49, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 48, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 8, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 38, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 46, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 27, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 6, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false))
    id = 48, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 49, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 26, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 35, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 17, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 48, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 18, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 19, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
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
  [%expect
    {|
    New variable:
    id = 58, level = 0 is_generic = false, scope = 0
    New variable:
    id = 59, level = 0 is_generic = false, scope = 0
    New variable:
    id = 60, level = 0 is_generic = false, scope = 0
    New former:
    id = 61, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 58 61
    Before exit:
    Current level: 1
    Region 0
    id = 60, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 58, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 59, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 58, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    Scope Array order:

    Array order:

    After exit:
    Current level: 0
    Region 0
    id = 60, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 58, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 59, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 58, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    Unify: 60 59
    Before exit:
    Current level: 0
    Region 0
    id = 60, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 58, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 60, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 58, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    Scope Array order:
    58,60,58,60
    Array order:
    58,60,58,60
    After exit:
    Current level: -1
    Region 0
    Region 1
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
  [%expect
    {|
    New variable:
    id = 62, level = 0 is_generic = false, scope = 0
    New variable:
    id = 63, level = 0 is_generic = false, scope = 0
    New variable:
    id = 64, level = 0 is_generic = false, scope = 0
    New former:
    id = 65, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 62 65
    Before exit:
    Current level: 1
    Region 0
    id = 62, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 63, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 62, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 64, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    Scope Array order:

    Array order:

    After exit:
    Current level: 0
    Region 0
    id = 62, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 63, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 62, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 64, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    New variable:
    id = 66, level = 0 is_generic = false, scope = 0
    New variable:
    id = 67, level = 0 is_generic = false, scope = 0
    New former:
    id = 68, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 64 68
    Before exit:
    Current level: 1
    Region 0
    id = 67, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 64, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 62, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 63, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 66, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 64, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    Scope Array order:

    Array order:

    After exit:
    Current level: 0
    Region 0
    id = 67, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 64, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 62, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 63, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 66, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 64, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    New variable:
    id = 69, level = 0 is_generic = false, scope = 0
    New variable:
    id = 70, level = 0 is_generic = false, scope = 0
    New former:
    id = 71, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 67 71
    Before exit:
    Current level: 1
    Region 0
    id = 67, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 64, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 62, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 69, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 63, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 66, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 70, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 67, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    Region 3
    Scope Array order:

    Array order:

    After exit:
    Current level: 0
    Region 0
    id = 67, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 64, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 62, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 69, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 63, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 66, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 70, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 67, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    Region 3
    New variable:
    id = 72, level = 0 is_generic = false, scope = 0
    New former:
    id = 73, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 73 63
    New variable:
    id = 74, level = 0 is_generic = false, scope = 0
    New variable:
    id = 75, level = 0 is_generic = false, scope = 0
    New former:
    id = 76, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    Unify: 72 76
    Unify: 74 66
    Unify: 75 69
    Before exit:
    Current level: 0
    Region 0
    id = 67, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 72, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 64, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 72, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 75, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 62, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Arrow((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 75, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 74, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 73, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 74, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 70, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 67, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 73, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    Region 3
    Scope Array order:
    73,67,70,74,73,74,75,62,75,72,64,72,67
    Array order:
    73,67,70,74,73,74,75,62,75,72,64,72,67
    After exit:
    Current level: -1
    Region 0
    Region 1
    Region 2
    Region 3
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
  [%expect
    {|
    New variable:
    id = 77, level = 0 is_generic = false, scope = 0
    New variable:
    id = 78, level = 0 is_generic = false, scope = 0
    New variable:
    id = 79, level = 0 is_generic = false, scope = 0
    New former:
    id = 80, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 77 80
    Before exit:
    Current level: 1
    Region 0
    id = 77, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 78, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 77, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 79, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    Scope Array order:

    Array order:

    After exit:
    Current level: 0
    Region 0
    id = 77, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 78, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 77, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 79, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
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
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 79 85
    New former:
    id = 86, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    Unify: 81 86
    Before exit:
    Current level: 1
    Region 0
    id = 81, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 83, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 84, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 77, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 79, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 81, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 78, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 82, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    Scope Array order:

    Array order:

    After exit:
    Current level: 0
    Region 0
    id = 81, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 83, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 84, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 77, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 79, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 81, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 78, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 82, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    New variable:
    id = 87, level = 0 is_generic = false, scope = 0
    New former:
    id = 88, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New variable:
    id = 89, level = 0 is_generic = false, scope = 0
    New former:
    id = 90, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 90 78
    Unify: 89 84
    Unify: 87 83
    Before exit:
    Current level: 0
    Region 0
    id = 81, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 88, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 87, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 89, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 77, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 87, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 79, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 81, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 90, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 90, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 89, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 82, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    Scope Array order:
    82,89,90,90,81,79,87,77,89,87,88,81
    Array order:
    82,89,90,90,81,79,87,77,89,87,88,81
    After exit:
    Current level: -1
    Region 0
    Region 1
    Region 2
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
  [%expect
    {|
    New variable:
    id = 91, level = 0 is_generic = false, scope = 0
    New variable:
    id = 92, level = 0 is_generic = false, scope = 0
    New variable:
    id = 93, level = 0 is_generic = false, scope = 0
    New former:
    id = 94, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 91 94
    Before exit:
    Current level: 1
    Region 0
    id = 92, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 93, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 91, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 91, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    Scope Array order:

    Array order:

    After exit:
    Current level: 0
    Region 0
    id = 92, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 93, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 91, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 91, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    New variable:
    id = 95, level = 0 is_generic = false, scope = 0
    New variable:
    id = 96, level = 0 is_generic = false, scope = 0
    New former:
    id = 97, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 93 97
    Before exit:
    Current level: 1
    Region 0
    id = 93, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 96, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 92, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 95, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 93, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 91, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    Scope Array order:

    Array order:

    After exit:
    Current level: 0
    Region 0
    id = 93, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 96, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 92, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 95, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 93, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 91, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    New variable:
    id = 98, level = 0 is_generic = false, scope = 0
    New variable:
    id = 99, level = 0 is_generic = false, scope = 0
    New former:
    id = 100, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 96 100
    Before exit:
    Current level: 1
    Region 0
    id = 93, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 96, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 99, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 91, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 98, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 92, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 96, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 95, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    Region 3
    Scope Array order:

    Array order:

    After exit:
    Current level: 0
    Region 0
    id = 93, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 96, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 99, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 91, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 98, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 92, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 96, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 95, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    Region 3
    New variable:
    id = 101, level = 0 is_generic = false, scope = 0
    New former:
    id = 102, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 102 92
    New variable:
    id = 103, level = 0 is_generic = false, scope = 0
    New former:
    id = 104, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 104 95
    Unify: 103 98
    Before exit:
    Current level: 0
    Region 0
    id = 93, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 96, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 99, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 102, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 103, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 101, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 91, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 103, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 104, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 102, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 96, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 104, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    Region 3
    Scope Array order:
    104,96,102,104,103,91,101,103,102,99,96,93
    Array order:
    104,96,102,104,103,91,101,103,102,99,96,93
    After exit:
    Current level: -1
    Region 0
    Region 1
    Region 2
    Region 3
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
  [%expect
    {|
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
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 105 110
    New former:
    id = 111, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    Unify: 106 111
    Before exit:
    Current level: 1
    Region 0
    id = 105, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 109, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 106, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 106, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 107, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 108, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 105, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    Scope Array order:

    Array order:

    After exit:
    Current level: 0
    Region 0
    id = 105, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 109, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 106, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 106, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 107, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 108, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 105, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    Unify: 107 109
    Before exit:
    Current level: 0
    Region 0
    id = 105, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 107, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 106, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 106, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 107, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 108, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 105, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    Scope Array order:
    105,108,107,106,106,107,105
    Array order:
    105,108,107,106,106,107,105
    After exit:
    Current level: -1
    Region 0
    Region 1
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
  [%expect
    {|
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
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 112 117
    New former:
    id = 118, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    Unify: 113 118
    Before exit:
    Current level: 1
    Region 0
    id = 113, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 114, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 115, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 113, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 112, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 116, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 112, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    Scope Array order:

    Array order:

    After exit:
    Current level: 0
    Region 0
    id = 113, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 114, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 115, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 113, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 112, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 116, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 112, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    Unify: 114 115
    Before exit:
    Current level: 0
    Region 0
    id = 113, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 114, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 114, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 113, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 112, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 116, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 112, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    Scope Array order:
    112,116,112,113,114,114,113
    Array order:
    112,116,112,113,114,114,113
    After exit:
    Current level: -1
    Region 0
    Region 1
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
  [%expect
    {|
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
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 124, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 125, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))
    New variable:
    id = 126, level = 0 is_generic = false, scope = 0
    New variable:
    id = 127, level = 0 is_generic = false, scope = 0
    New former:
    id = 128, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 119 128
    Unify: 120 125
    New former:
    id = 129, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    Unify: 124 129
    Before exit:
    Current level: 1
    Region 0
    id = 120, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))
    id = 119, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 122, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 123, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))
    id = 123, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))
    id = 120, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))
    id = 121, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 119, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 124, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 124, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 122, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    Scope Array order:

    Array order:

    After exit:
    Current level: 0
    Region 0
    id = 120, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))
    id = 119, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 122, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 123, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))
    id = 123, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))
    id = 120, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))
    id = 121, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 119, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 124, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 124, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 122, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    Unify: 121 122
    Before exit:
    Current level: 0
    Region 0
    id = 120, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))
    id = 119, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 121, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 123, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))
    id = 123, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))
    id = 120, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))
    id = 121, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 119, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 124, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 124, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))))))(scope 0)))(level 0)(is_generic false))
    id = 121, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    Scope Array order:
    121,124,124,119,121,120,123,123,121,119,120
    Array order:
    121,124,124,119,121,120,123,123,121,119,120
    After exit:
    Current level: -1
    Region 0
    Region 1
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
  [%expect
    {|
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
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 130 134
    Unify: 132 131
    Before exit:
    Current level: 1
    Region 0
    id = 132, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 130, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 130, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 133, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 132, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    Scope Array order:

    Array order:

    After exit:
    Current level: 0
    Region 0
    id = 132, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 130, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 130, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 133, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 132, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    Unify: 133 132
    Before exit:
    Current level: 0
    Region 0
    id = 133, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 130, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 130, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 133, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 133, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    Scope Array order:
    133,133,130,130,133
    Array order:
    133,133,130,130,133
    After exit:
    Current level: -1
    Region 0
    Region 1
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
  [%expect
    {|
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
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 136 139
    New rigid variable: 0
    id = 140, level = 1 is_generic = false, scope = 0
    Unify: 137 140
    New rigid variable: 0
    id = 141, level = 2 is_generic = false, scope = 0
    Before exit:
    Current level: 2
    Region 0
    id = 135, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 136, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Rigid_var 0))(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 138, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 137, level = 1 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 0))(scope 0)))(level 1)(is_generic false))
    id = 137, level = 1 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 0))(scope 0)))(level 1)(is_generic false))
    Region 2
    id = 141, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 0))(scope 0)))(level 2)(is_generic false))
    Scope Array order:
    141
    Array order:
    141
    After exit:
    Current level: 1
    Region 0
    id = 135, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 136, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Rigid_var 0))(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 138, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 137, level = 1 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 0))(scope 0)))(level 1)(is_generic false))
    id = 137, level = 1 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 0))(scope 0)))(level 1)(is_generic false))
    Region 2
    New rigid variable: 0
    id = 142, level = 1 is_generic = false, scope = 0
    Unify: 138 142
    Before exit:
    Current level: 1
    Region 0
    id = 135, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 136, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Rigid_var 0))(scope 0)))(level 1)(is_generic false))((structure((desc(Rigid_var 0))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 138, level = 1 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 0))(scope 0)))(level 1)(is_generic false))
    id = 137, level = 1 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 0))(scope 0)))(level 1)(is_generic false))
    id = 137, level = 1 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 0))(scope 0)))(level 1)(is_generic false))
    id = 138, level = 1 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 0))(scope 0)))(level 1)(is_generic false))
    Region 2
    Scope Array order:
    138,137,137,138,136
    Array order:
    138,137,137,138,136
    New variable:
    id = 143, level = 1 is_generic = false, scope = 0
    Unify: 138 143
    Unify: 137 138
    Unify: 141 137
    After exit:
    Current level: 0
    Region 0
    id = 135, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 141, level = 1 is_generic = true, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic true))
    Region 2
    New variable:
    id = 144, level = 0 is_generic = false, scope = 0
    New former:
    id = 145, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 135 145
    Before exit:
    Current level: 0
    Region 0
    id = 135, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 144, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 135, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 141, level = 1 is_generic = true, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic true))
    Region 2
    Scope Array order:
    135,144,135
    Array order:
    135,144,135
    After exit:
    Current level: -1
    Region 0
    Region 1
    id = 141, level = 1 is_generic = true, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic true))
    Region 2
    Variables: α144
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Variable: α144
          └──Type expr: Variable: α144
       └──Desc: Function
          └──Pattern:
             └──Type expr: Variable: α141
             └──Desc: Variable: x
          └──Expression:
             └──Type expr: Variable: α141
             └──Desc: Variable
                └──Variable: x |}]

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
  [%expect
    {|
    New variable:
    id = 146, level = 0 is_generic = false, scope = 0
    New variable:
    id = 147, level = 0 is_generic = false, scope = 0
    New variable:
    id = 148, level = 0 is_generic = false, scope = 0
    New variable:
    id = 149, level = 0 is_generic = false, scope = 0
    New former:
    id = 150, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 146 150
    Unify: 148 147
    Before exit:
    Current level: 1
    Region 0
    id = 148, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 146, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 148, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 146, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 149, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    Scope Array order:

    Array order:

    After exit:
    Current level: 0
    Region 0
    id = 148, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 146, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 148, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 146, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 149, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    New variable:
    id = 151, level = 0 is_generic = false, scope = 0
    New former:
    id = 152, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New variable:
    id = 153, level = 0 is_generic = false, scope = 0
    New former:
    id = 154, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 155, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 156, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 157, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 158, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 159, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 154 159
    Unify: 153 148
    New former:
    id = 160, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    Unify: 151 160
    Before exit:
    Current level: 0
    Region 0
    id = 153, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 146, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 151, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 152, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 154, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 153, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 153, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 152, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 151, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 149, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 149, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 154, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 151, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    Region 1
    Scope Array order:
    151,154,149,149,151,152,153,153,154,152,151,146,153
    Array order:
    151,154,149,149,151,152,153,153,154,152,151,146,153
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
  [%expect
    {|
    New variable:
    id = 161, level = 0 is_generic = false, scope = 0
    New variable:
    id = 162, level = 1 is_generic = false, scope = 0
    Solver: bind_rigid
    New variable:
    id = 163, level = 1 is_generic = false, scope = 0
    New variable:
    id = 164, level = 1 is_generic = false, scope = 0
    New former:
    id = 165, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 162 165
    New rigid variable: 1
    id = 166, level = 1 is_generic = false, scope = 0
    Unify: 163 166
    New rigid variable: 1
    id = 167, level = 2 is_generic = false, scope = 0
    Before exit:
    Current level: 2
    Region 0
    id = 161, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 164, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 163, level = 1 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 1))(scope 0)))(level 1)(is_generic false))
    id = 162, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Rigid_var 1))(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 163, level = 1 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 1))(scope 0)))(level 1)(is_generic false))
    Region 2
    id = 167, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 1))(scope 0)))(level 2)(is_generic false))
    Scope Array order:
    167
    Array order:
    167
    After exit:
    Current level: 1
    Region 0
    id = 161, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 164, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 163, level = 1 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 1))(scope 0)))(level 1)(is_generic false))
    id = 162, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Rigid_var 1))(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 163, level = 1 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 1))(scope 0)))(level 1)(is_generic false))
    Region 2
    New variable:
    id = 168, level = 1 is_generic = false, scope = 0
    New former:
    id = 169, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    New variable:
    id = 170, level = 1 is_generic = false, scope = 0
    New former:
    id = 171, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 172, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 173, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 174, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 175, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 176, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 171 176
    New rigid variable: 1
    id = 177, level = 1 is_generic = false, scope = 0
    Unify: 170 177
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
  [%expect
    {|
    New variable:
    id = 178, level = 0 is_generic = false, scope = 0
    New variable:
    id = 179, level = 1 is_generic = false, scope = 0
    New variable:
    id = 180, level = 1 is_generic = false, scope = 0
    New variable:
    id = 181, level = 1 is_generic = false, scope = 0
    New former:
    id = 182, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 179 182
    Before exit:
    Current level: 2
    Region 0
    id = 178, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 180, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 179, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 181, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 179, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Region 2
    Scope Array order:

    Array order:

    After exit:
    Current level: 1
    Region 0
    id = 178, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 180, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 179, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 181, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 179, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Region 2
    Unify: 181 180
    Before exit:
    Current level: 1
    Region 0
    id = 178, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 181, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 179, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 181, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 179, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Region 2
    Scope Array order:
    179,181,179,181
    Array order:
    179,181,179,181
    After exit:
    Current level: 0
    Region 0
    id = 178, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    New variable:
    id = 183, level = 0 is_generic = false, scope = 0
    New former:
    id = 184, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New variable:
    id = 185, level = 0 is_generic = false, scope = 0
    New former:
    id = 186, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New variable:
    id = 187, level = 0 is_generic = false, scope = 0
    New former:
    id = 188, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 186 188
    New variable:
    id = 189, level = 0 is_generic = false, scope = 0
    New former:
    id = 190, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 184 190
    New former:
    id = 191, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()unit)))(scope 0)))(level 0)(is_generic false))
    Unify: 178 191
    Before exit:
    Current level: 0
    Region 0
    id = 184, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()unit)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()unit)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 178, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()unit)))(scope 0)))(level 0)(is_generic false))
    id = 186, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()unit)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()unit)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()unit)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()unit)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 178, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()unit)))(scope 0)))(level 0)(is_generic false))
    id = 178, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()unit)))(scope 0)))(level 0)(is_generic false))
    id = 184, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()unit)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()unit)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 178, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()unit)))(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    Scope Array order:
    178,184,178,178,186,178,184
    Array order:
    178,184,178,178,186,178,184
    After exit:
    Current level: -1
    Region 0
    Region 1
    Region 2
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Constructor: unit
       └──Desc: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: α181
                      └──Type expr: Variable: α181
                   └──Desc: Variable: id
                └──Abstraction:
                   └──Variables: α181
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: α181
                         └──Type expr: Variable: α181
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: α181
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: α181
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
  [%expect
    {|
    New variable:
    id = 192, level = 0 is_generic = false, scope = 0
    New variable:
    id = 193, level = 1 is_generic = false, scope = 0
    New variable:
    id = 194, level = 1 is_generic = false, scope = 0
    New variable:
    id = 195, level = 1 is_generic = false, scope = 0
    New former:
    id = 196, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 193 196
    Before exit:
    Current level: 2
    Region 0
    id = 192, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 194, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 195, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 193, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 193, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Region 2
    Scope Array order:

    Array order:

    After exit:
    Current level: 1
    Region 0
    id = 192, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 194, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 195, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 193, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 193, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Region 2
    New variable:
    id = 197, level = 1 is_generic = false, scope = 0
    New variable:
    id = 198, level = 1 is_generic = false, scope = 0
    New former:
    id = 199, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 195 199
    Before exit:
    Current level: 2
    Region 0
    id = 192, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 195, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 197, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 195, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 194, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 198, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 193, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Region 2
    Region 3
    Scope Array order:

    Array order:

    After exit:
    Current level: 1
    Region 0
    id = 192, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 195, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 197, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 195, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 194, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 198, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 193, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Region 2
    Region 3
    New variable:
    id = 200, level = 1 is_generic = false, scope = 0
    Unify: 200 197
    New variable:
    id = 201, level = 1 is_generic = false, scope = 0
    New former:
    id = 202, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    Unify: 200 202
    Before exit:
    Current level: 2
    Region 0
    id = 192, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 195, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 201, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 193, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 200, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    id = 200, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    id = 194, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 198, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    Region 2
    Region 3
    Region 4
    Scope Array order:

    Array order:

    After exit:
    Current level: 1
    Region 0
    id = 192, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 195, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 201, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 193, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 200, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    id = 200, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    id = 194, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 198, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    Region 2
    Region 3
    Region 4
    New variable:
    id = 203, level = 1 is_generic = false, scope = 0
    New former:
    id = 204, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    Unify: 198 204
    New variable:
    id = 205, level = 1 is_generic = false, scope = 0
    New former:
    id = 206, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 207, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))))))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 208, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    New variable:
    id = 209, level = 1 is_generic = false, scope = 0
    New variable:
    id = 210, level = 1 is_generic = false, scope = 0
    Unify: 200 208
    New former:
    id = 211, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))))))(scope 0)))(level 1)(is_generic false))
    Unify: 207 211
    Before exit:
    Current level: 2
    Region 0
    id = 192, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 195, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 203, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 207, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))))))(scope 0)))(level 1)(is_generic false))
    id = 201, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 198, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    id = 206, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    id = 201, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 193, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 207, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))))))(scope 0)))(level 1)(is_generic false))
    id = 200, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    id = 206, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    id = 200, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    id = 200, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    id = 201, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 194, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 198, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    Region 2
    Region 3
    Region 4
    Region 5
    Scope Array order:

    Array order:

    After exit:
    Current level: 1
    Region 0
    id = 192, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 195, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 203, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 207, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))))))(scope 0)))(level 1)(is_generic false))
    id = 201, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 198, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    id = 206, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    id = 201, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 193, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 207, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))))))(scope 0)))(level 1)(is_generic false))
    id = 200, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    id = 206, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    id = 200, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    id = 200, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    id = 201, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 194, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 198, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    Region 2
    Region 3
    Region 4
    Region 5
    New variable:
    id = 212, level = 1 is_generic = false, scope = 0
    New former:
    id = 213, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 214, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))))))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 215, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    Unify: 198 215
    New variable:
    id = 216, level = 1 is_generic = false, scope = 0
    New variable:
    id = 217, level = 1 is_generic = false, scope = 0
    New former:
    id = 218, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))))))(scope 0)))(level 1)(is_generic false))
    Unify: 214 218
    New variable:
    id = 219, level = 1 is_generic = false, scope = 0
    New former:
    id = 220, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 220 194
    Unify: 219 201
    New variable:
    id = 221, level = 1 is_generic = false, scope = 0
    New former:
    id = 222, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    New variable:
    id = 223, level = 1 is_generic = false, scope = 0
    New former:
    id = 224, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 224 193
    Unify: 223 223
    Unify: 221 206
    Before exit:
    Current level: 1
    Region 0
    id = 192, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 222, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 203, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 219, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 207, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))))))(scope 0)))(level 1)(is_generic false))
    id = 223, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 203, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 224, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 203, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 214, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))))))(scope 0)))(level 1)(is_generic false))
    id = 213, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    id = 223, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 213, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    id = 221, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    id = 213, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    id = 223, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 221, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    id = 224, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 219, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 221, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    id = 214, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Tuple(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))))))(scope 0)))(level 1)(is_generic false))
    id = 213, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))
    id = 222, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))list)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Region 2
    Region 3
    Region 4
    Region 5
    Scope Array order:
    222,213,214,221,219,224,221,223,213,221,213,223,213,214,203,224,203,223,207,219,203,222
    Array order:
    222,213,214,221,219,224,221,223,213,221,213,223,213,214,203,224,203,223,207,219,203,222
    After exit:
    Current level: 0
    Region 0
    id = 192, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    Region 3
    Region 4
    Region 5
    New variable:
    id = 225, level = 1 is_generic = false, scope = 0
    New variable:
    id = 226, level = 1 is_generic = false, scope = 0
    New variable:
    id = 227, level = 1 is_generic = false, scope = 0
    New former:
    id = 228, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 225 228
    Before exit:
    Current level: 2
    Region 0
    id = 192, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 225, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 226, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 225, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 227, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    Region 2
    Region 3
    Region 4
    Region 5
    Region 6
    Region 7
    Scope Array order:

    Array order:

    After exit:
    Current level: 1
    Region 0
    id = 192, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 225, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 226, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 225, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 227, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    Region 2
    Region 3
    Region 4
    Region 5
    Region 6
    Region 7
    New variable:
    id = 229, level = 1 is_generic = false, scope = 0
    New former:
    id = 230, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    New variable:
    id = 231, level = 1 is_generic = false, scope = 0
    New former:
    id = 232, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 233, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 234, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 235, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 236, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 237, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 232 237
    Unify: 231 226
    New former:
    id = 238, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    Unify: 229 238
    Before exit:
    Current level: 1
    Region 0
    id = 192, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 227, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 229, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 225, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 229, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 232, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 231, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 232, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 231, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 230, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 231, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 230, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 225, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 227, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 229, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    Region 2
    Region 3
    Region 4
    Region 5
    Region 6
    Region 7
    Scope Array order:
    229,227,225,230,231,230,231,232,231,232,229,225,229,227
    Array order:
    229,227,225,230,231,230,231,232,231,232,229,225,229,227
    After exit:
    Current level: 0
    Region 0
    id = 225, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 229, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 231, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 192, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 227, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 230, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 232, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    Region 3
    Region 4
    Region 5
    Region 6
    Region 7
    New variable:
    id = 239, level = 0 is_generic = false, scope = 0
    New former:
    id = 240, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New variable:
    id = 241, level = 0 is_generic = false, scope = 0
    New former:
    id = 242, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New variable:
    id = 243, level = 0 is_generic = false, scope = 0
    New variable:
    id = 244, level = 0 is_generic = false, scope = 0
    New former:
    id = 245, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 246, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 247, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 248, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    New former:
    id = 249, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 242 249
    Unify: 241 225
    New variable:
    id = 250, level = 0 is_generic = false, scope = 0
    New former:
    id = 251, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))
    Unify: 239 251
    Before exit:
    Current level: 0
    Region 0
    id = 192, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))
    id = 241, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 239, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))
    id = 239, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))
    id = 241, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 229, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 192, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))
    id = 232, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 243, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 243, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 241, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 240, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr(((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 244, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 230, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 243, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 242, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr(((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 240, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr(((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 244, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 239, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))
    id = 242, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr(((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))list)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    Region 3
    Region 4
    Region 5
    Region 6
    Region 7
    Scope Array order:
    242,239,244,240,242,243,230,244,240,241,243,243,232,192,229,241,239,239,241,192
    Array order:
    242,239,244,240,242,243,230,244,240,241,243,243,232,192,229,241,239,239,241,192
    After exit:
    Current level: -1
    Region 0
    Region 1
    Region 2
    Region 3
    Region 4
    Region 5
    Region 6
    Region 7
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
                   └──Variables: α203,α219
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: α219
                            └──Type expr: Variable: α203
                         └──Type expr: Arrow
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: α219
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: α203
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Variable: α219
                               └──Type expr: Variable: α203
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: α219
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: α203
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: α219
                                  └──Desc: Variable: xs
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: α203
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Variable: α219
                                        └──Desc: Variable
                                           └──Variable: xs
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: α219
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: α219
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α219
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: α203
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α203
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: α219
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: α219
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: α219
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α219
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: α219
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α219
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Variable: α219
                                                          └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: α219
                                                          └──Desc: Variable: xs
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: α203
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: α203
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: α203
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α203
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: α203
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α203
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Variable: α203
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: α219
                                                                   └──Type expr: Variable: α203
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Variable: α219
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: α203
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: α219
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: α203
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Variable: α219
                                                                            └──Type expr: Variable: α203
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: α219
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: α203
                                                                      └──Desc: Variable
                                                                         └──Variable: map
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: α219
                                                                         └──Type expr: Variable: α203
                                                                      └──Desc: Variable
                                                                         └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: α219
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
  [%expect
    {|
    New variable:
    id = 252, level = 0 is_generic = false, scope = 0
    New variable:
    id = 253, level = 1 is_generic = false, scope = 0
    New variable:
    id = 254, level = 1 is_generic = false, scope = 0
    New variable:
    id = 255, level = 1 is_generic = false, scope = 0
    New variable:
    id = 256, level = 1 is_generic = false, scope = 0
    New former:
    id = 257, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 253 257
    Before exit:
    Current level: 2
    Region 0
    id = 252, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 254, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 256, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 253, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 255, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 253, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Region 2
    Scope Array order:

    Array order:

    After exit:
    Current level: 1
    Region 0
    id = 252, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 254, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 256, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 253, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 255, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 253, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Region 2
    Unify: 256 255
    New variable:
    id = 258, level = 1 is_generic = false, scope = 0
    New variable:
    id = 259, level = 1 is_generic = false, scope = 0
    New former:
    id = 260, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 254 260
    Before exit:
    Current level: 2
    Region 0
    id = 252, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 254, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 256, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 259, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 253, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 254, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 256, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 253, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 258, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    Region 2
    Region 3
    Scope Array order:

    Array order:

    After exit:
    Current level: 1
    Region 0
    id = 252, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 254, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 256, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 259, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 253, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 254, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 256, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 253, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 258, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    Region 2
    Region 3
    New variable:
    id = 261, level = 1 is_generic = false, scope = 0
    New former:
    id = 262, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 262 253
    New former:
    id = 263, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 264, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    Unify: 259 264
    Unify: 263 258
    Before exit:
    Current level: 1
    Region 0
    id = 252, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 259, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 259, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 263, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 263, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 254, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 259, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 259, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 262, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 262, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Region 2
    Region 3
    Scope Array order:
    262,262,259,259,254,263,263,259,259
    Array order:
    262,262,259,259,254,263,263,259,259
    After exit:
    Current level: 0
    Region 0
    id = 254, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 252, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 259, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 263, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 262, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    Region 3
    Unify: 252 262
    Before exit:
    Current level: 0
    Region 0
    id = 254, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 252, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 259, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 263, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 252, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    Region 3
    Scope Array order:
    252,263,259,252,254
    Array order:
    252,263,259,252,254
    After exit:
    Current level: -1
    Region 0
    Region 1
    Region 2
    Region 3
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
  [%expect
    {|
    New variable:
    id = 265, level = 0 is_generic = false, scope = 0
    New variable:
    id = 266, level = 1 is_generic = false, scope = 0
    New variable:
    id = 267, level = 1 is_generic = false, scope = 0
    New variable:
    id = 268, level = 1 is_generic = false, scope = 0
    New variable:
    id = 269, level = 1 is_generic = false, scope = 0
    New former:
    id = 270, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 266 270
    Before exit:
    Current level: 2
    Region 0
    id = 265, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 269, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 268, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 266, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 266, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 267, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    Region 2
    Scope Array order:

    Array order:

    After exit:
    Current level: 1
    Region 0
    id = 265, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 269, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 268, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 266, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 266, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 267, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    Region 2
    New former:
    id = 271, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false))
    New variable:
    id = 272, level = 1 is_generic = false, scope = 0
    New former:
    id = 273, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    New variable:
    id = 274, level = 1 is_generic = false, scope = 0
    New former:
    id = 275, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 276, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 277, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 278, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 279, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 280, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 275 280
    Unify: 274 268
    New former:
    id = 281, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    Unify: 272 281
    New former:
    id = 282, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false))
    Unify: 269 282
    New variable:
    id = 283, level = 1 is_generic = false, scope = 0
    New former:
    id = 284, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 284 267
    New variable:
    id = 285, level = 1 is_generic = false, scope = 0
    New former:
    id = 286, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    New variable:
    id = 287, level = 1 is_generic = false, scope = 0
    New former:
    id = 288, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 289, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 290, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 291, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 292, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 293, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 288 293
    Unify: 287 274
    New former:
    id = 294, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    Unify: 285 294
    New variable:
    id = 295, level = 1 is_generic = false, scope = 0
    New variable:
    id = 296, level = 1 is_generic = false, scope = 0
    New former:
    id = 297, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 284 297
    Before exit:
    Current level: 2
    Region 0
    id = 265, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 288, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 271, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false))
    id = 284, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 284, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 287, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 269, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false))
    id = 287, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 275, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 287, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 285, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 283, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 283, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 286, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 266, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 272, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 284, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 269, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false))
    id = 273, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 283, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 285, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 286, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 288, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 285, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    Region 2
    Region 3
    Scope Array order:

    Array order:

    After exit:
    Current level: 1
    Region 0
    id = 265, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 288, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 271, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false))
    id = 284, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 284, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 287, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 269, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false))
    id = 287, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 275, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 287, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 285, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 283, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 283, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 286, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 266, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 272, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 284, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 269, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false))
    id = 273, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 283, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 285, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 286, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 288, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 285, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    Region 2
    Region 3
    New former:
    id = 298, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false))
    New variable:
    id = 299, level = 1 is_generic = false, scope = 0
    New former:
    id = 300, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    New variable:
    id = 301, level = 1 is_generic = false, scope = 0
    New former:
    id = 302, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 303, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 304, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 305, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 306, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 307, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 302 307
    Unify: 301 283
    New former:
    id = 308, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    Unify: 299 308
    New former:
    id = 309, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false))
    Unify: 269 309
    New variable:
    id = 310, level = 1 is_generic = false, scope = 0
    New former:
    id = 311, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 311 266
    New variable:
    id = 312, level = 1 is_generic = false, scope = 0
    New former:
    id = 313, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    New variable:
    id = 314, level = 1 is_generic = false, scope = 0
    New former:
    id = 315, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 316, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 317, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 318, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 319, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 320, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 315 320
    Unify: 314 301
    New former:
    id = 321, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    Unify: 312 321
    Before exit:
    Current level: 1
    Region 0
    id = 265, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 315, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 315, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 271, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false))
    id = 312, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 302, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 310, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 299, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 269, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false))
    id = 314, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 300, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 273, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 285, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 311, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 314, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 286, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 298, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false))
    id = 298, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false))
    id = 288, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 312, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 313, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 275, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 300, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 299, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 314, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 312, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 311, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 272, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 284, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 269, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false))
    id = 313, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 302, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 310, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 314, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 299, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 310, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 314, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    Region 2
    Region 3
    Scope Array order:
    314,310,299,314,310,302,313,269,284,272,311,312,314,299,300,275,313,312,288,298,298,286,314,311,285,273,300,314,269,299,310,302,312,271,315,315
    Array order:
    314,310,299,314,310,302,313,269,284,272,311,312,314,299,300,275,313,312,288,298,298,286,314,311,285,273,300,314,269,299,310,302,312,271,315,315
    After exit:
    Current level: 0
    Region 0
    id = 288, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 315, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 271, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false))
    id = 312, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 275, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 299, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 300, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 265, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 314, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 272, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 284, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 269, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false))
    id = 273, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 285, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 311, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 313, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 302, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 310, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 286, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 298, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    Region 3
    Unify: 265 311
    Before exit:
    Current level: 0
    Region 0
    id = 288, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 315, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 271, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false))
    id = 312, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 275, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 299, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 300, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 265, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 314, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 272, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 284, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 269, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false))
    id = 273, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 285, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 265, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 313, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 302, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 310, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 286, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 298, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    Region 3
    Scope Array order:
    298,286,310,302,313,265,285,273,269,284,272,314,265,300,299,275,312,271,315,288
    Array order:
    298,286,310,302,313,265,285,273,269,284,272,314,265,300,299,275,312,271,315,288
    After exit:
    Current level: -1
    Region 0
    Region 1
    Region 2
    Region 3
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
  [%expect
    {|
    New variable:
    id = 322, level = 0 is_generic = false, scope = 0
    New variable:
    id = 323, level = 1 is_generic = false, scope = 0
    New variable:
    id = 324, level = 1 is_generic = false, scope = 0
    New variable:
    id = 325, level = 1 is_generic = false, scope = 0
    New variable:
    id = 326, level = 1 is_generic = false, scope = 0
    New former:
    id = 327, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 323 327
    Before exit:
    Current level: 2
    Region 0
    id = 322, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 323, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 324, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 325, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 326, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 323, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Region 2
    Scope Array order:

    Array order:

    After exit:
    Current level: 1
    Region 0
    id = 322, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 323, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 324, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 325, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 326, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 323, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Region 2
    New former:
    id = 328, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    Unify: 326 328
    New variable:
    id = 329, level = 1 is_generic = false, scope = 0
    New variable:
    id = 330, level = 1 is_generic = false, scope = 0
    New former:
    id = 331, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 324 331
    Before exit:
    Current level: 2
    Region 0
    id = 322, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 329, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 330, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 324, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 325, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 324, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 326, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 323, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Region 2
    Region 3
    Scope Array order:

    Array order:

    After exit:
    Current level: 1
    Region 0
    id = 322, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 329, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 330, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 324, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 325, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 324, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 326, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 323, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Region 2
    Region 3
    New former:
    id = 332, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false))
    Unify: 330 332
    Before exit:
    Current level: 1
    Region 0
    id = 322, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 329, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 330, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false))
    id = 330, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false))
    id = 324, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 325, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 324, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()bool)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 326, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false))
    id = 323, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Region 2
    Region 3
    Scope Array order:
    323,326,324,325,324,330,330,329
    Array order:
    323,326,324,325,324,330,330,329
    After exit:
    Current level: 0
    Region 0
    id = 322, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 326, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 330, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    Region 3
    New variable:
    id = 333, level = 0 is_generic = false, scope = 0
    New former:
    id = 334, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    Unify: 322 334
    Before exit:
    Current level: 0
    Region 0
    id = 330, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()bool)))(scope 0)))(level 0)(is_generic false))
    id = 322, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 322, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false)))))(scope 0)))(level 0)(is_generic false))
    id = 326, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()int)))(scope 0)))(level 0)(is_generic false))
    id = 333, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    Region 3
    Scope Array order:
    333,326,322,322,330
    Array order:
    333,326,322,322,330
    After exit:
    Current level: -1
    Region 0
    Region 1
    Region 2
    Region 3
    Variables: α333
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Variable: α333
          └──Type expr: Constructor: int
       └──Desc: Let rec
          └──Value bindings:
             └──Value binding:
                └──Variable: bar
                └──Abstraction:
                   └──Variables: α329
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: α325
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: α325
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Constant: 1
             └──Value binding:
                └──Variable: foo
                └──Abstraction:
                   └──Variables: α325
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: α329
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: α329
                            └──Desc: Variable: y
                         └──Expression:
                            └──Type expr: Constructor: bool
                            └──Desc: Constant: true
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Variable: α333
                └──Type expr: Constructor: int
             └──Desc: Variable
                └──Variable: foo
                └──Type expr: Variable: α333 |}]

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
  [%expect
    {|
    New variable:
    id = 335, level = 0 is_generic = false, scope = 0
    New variable:
    id = 336, level = 1 is_generic = false, scope = 0
    New variable:
    id = 337, level = 1 is_generic = false, scope = 0
    New former:
    id = 338, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    New variable:
    id = 339, level = 1 is_generic = false, scope = 0
    New variable:
    id = 340, level = 1 is_generic = false, scope = 0
    New former:
    id = 341, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 338 341
    Before exit:
    Current level: 2
    Region 0
    id = 335, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 338, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 338, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 336, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 337, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 336, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 337, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    Region 2
    Scope Array order:

    Array order:

    After exit:
    Current level: 1
    Region 0
    id = 335, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 338, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 338, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 336, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 337, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 336, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 337, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    Region 2
    New former:
    id = 342, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()unit)))(scope 0)))(level 1)(is_generic false))
    Unify: 336 342
    New variable:
    id = 343, level = 1 is_generic = false, scope = 0
    New variable:
    id = 344, level = 1 is_generic = false, scope = 0
    New former:
    id = 345, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 337 345
    Before exit:
    Current level: 2
    Region 0
    id = 335, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 338, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()unit)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 336, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()unit)))(scope 0)))(level 1)(is_generic false))
    id = 337, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 344, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 337, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 343, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    Region 2
    Region 3
    Scope Array order:

    Array order:

    After exit:
    Current level: 1
    Region 0
    id = 335, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 338, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()unit)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 336, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()unit)))(scope 0)))(level 1)(is_generic false))
    id = 337, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 344, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 337, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 343, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    Region 2
    Region 3
    Unify: 344 343
    Before exit:
    Current level: 1
    Region 0
    id = 335, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 338, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr()unit)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 336, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()unit)))(scope 0)))(level 1)(is_generic false))
    id = 337, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 344, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 337, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 344, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    Region 2
    Region 3
    Scope Array order:
    344,337,344,337,336,338
    Array order:
    344,337,344,337,336,338
    After exit:
    Current level: 0
    Region 0
    id = 335, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    id = 336, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()unit)))(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    Region 3
    Unify: 335 336
    Before exit:
    Current level: 0
    Region 0
    id = 335, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()unit)))(scope 0)))(level 0)(is_generic false))
    id = 335, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()unit)))(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    Region 3
    Scope Array order:
    335,335
    Array order:
    335,335
    After exit:
    Current level: -1
    Region 0
    Region 1
    Region 2
    Region 3
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
                   └──Variables: α344
                   └──Expression:
                      └──Type expr: Constructor: unit
                      └──Desc: Application
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: α344
                                  └──Type expr: Variable: α344
                               └──Type expr: Constructor: unit
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: α344
                                     └──Type expr: Variable: α344
                                  └──Desc: Variable: f
                               └──Expression:
                                  └──Type expr: Constructor: unit
                                  └──Desc: Constant: ()
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: α344
                               └──Type expr: Variable: α344
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: α344
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Variable: α344
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
  (* let coerce = forall a b -> fun eq x -> match (eq : (a, b) eq) with Refl -> (x : b) in () *)
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
                        ( Ppat_constraint
                            (Ppat_var "x", Ptyp_constr ([ Ptyp_var "a" ], "t"))
                        , Pexp_match
                            ( Pexp_constraint
                                ( Pexp_var "eq"
                                , Ptyp_constr
                                    ([ Ptyp_var "a"; Ptyp_var "b" ], "eq") )
                            , [ { pc_lhs = Ppat_construct ("Refl", None)
                                ; pc_rhs =
                                    Pexp_constraint
                                      ( Pexp_var "x"
                                      , Ptyp_constr ([ Ptyp_var "b" ], "t") )
                                }
                              ] ) ) ) )
          }
        ]
      , Pexp_const Const_unit )
  in
  print_constraint_result ~env exp;
  print_infer_result ~env exp;
  [%expect
    {|
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
                          ((Exist ((347 ((Arrow 332 333))))) ((Eq 331) 347)))
                         ((Conj (Map ((Conj (Map True)) (Decode 332))))
                          ((Def ((eq 332)))
                           ((Def_poly ()) ()
                            (Map
                             ((Conj
                               ((Exist
                                 ((334 ()) (335 ()) (336 ((Constr (329) t)))))
                                (Map
                                 ((Conj
                                   ((Exist ((346 ((Arrow 334 335)))))
                                    ((Eq 333) 346)))
                                  ((Conj
                                    (Map
                                     ((Conj
                                       (Map ((Conj ((Eq 334) 336)) (Map True))))
                                      (Decode 334))))
                                   ((Def ())
                                    ((Def_poly ((337 ((Constr (329) t)))))
                                     ((x 337))
                                     (Map
                                      ((Conj
                                        ((Exist ((338 ())))
                                         (Map
                                          ((Conj
                                            (Map
                                             ((Conj
                                               ((Exist
                                                 ((339 ((Constr (329 330) eq)))
                                                  (340 ((Constr (329 330) eq)))))
                                                (Map
                                                 ((Conj ((Eq 338) 340))
                                                  (Map ((Instance eq) 339))))))
                                              (Decode 338))))
                                           ((Conj (Decode 338))
                                            (Map
                                             ((Conj
                                               (Map
                                                ((Exist
                                                  ((341 ()) (342 ())
                                                   (343 ((Constr (341 342) eq)))))
                                                 (Map
                                                  ((Conj
                                                    (Map
                                                     ((Conj
                                                       (Map
                                                        ((Conj
                                                          (Map
                                                           ((Conj ((Eq 338) 343))
                                                            (Map
                                                             ((Conj (Decode 338))
                                                              (Map True))))))
                                                         (Map True))))
                                                      (Decode 338))))
                                                   ((Implication
                                                     (((Var 341) (Var 342))))
                                                    ((Def ())
                                                     ((Def_poly ()) ()
                                                      (Map
                                                       ((Conj
                                                         ((Exist
                                                           ((344
                                                             ((Constr (330) t)))
                                                            (345
                                                             ((Constr (330) t)))))
                                                          (Map
                                                           ((Conj ((Eq 335) 345))
                                                            (Map
                                                             ((Instance x) 344))))))
                                                        (Decode 335)))))))))))
                                              (Map True))))))))
                                       (Decode 335))))))))))
                              (Decode 333))))))))))))
                   ((Instance @dromedary.internal.pexp_forall) 328))))
                (Decode 328)))))))
          (Map
           ((Conj (Map ((Exist ((348 ((Constr () unit))))) ((Eq 327) 348))))
            (Decode 327))))))
       (Decode 327))))
    New variable:
    id = 346, level = 0 is_generic = false, scope = 0
    New variable:
    id = 347, level = 1 is_generic = false, scope = 0
    New variable:
    id = 348, level = 2 is_generic = false, scope = 0
    Solver: bind_rigid
    Solver: bind_rigid
    New variable:
    id = 349, level = 2 is_generic = false, scope = 0
    New variable:
    id = 350, level = 2 is_generic = false, scope = 0
    New former:
    id = 351, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false))
    Unify: 348 351
    Before exit:
    Current level: 3
    Region 0
    id = 346, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 347, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    Region 2
    id = 348, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false))
    id = 348, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false))
    id = 350, level = 2 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false))
    id = 349, level = 2 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false))
    Region 3
    Scope Array order:

    Array order:

    After exit:
    Current level: 2
    Region 0
    id = 346, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 347, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    Region 2
    id = 348, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false))
    id = 348, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false))
    id = 350, level = 2 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false))
    id = 349, level = 2 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false))
    Region 3
    New variable:
    id = 352, level = 2 is_generic = false, scope = 0
    New variable:
    id = 353, level = 2 is_generic = false, scope = 0
    New rigid variable: 2
    id = 354, level = 2 is_generic = false, scope = 0
    New former:
    id = 355, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))
    New former:
    id = 356, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false))
    Unify: 350 356
    Unify: 352 355
    New rigid variable: 2
    id = 357, level = 3 is_generic = false, scope = 0
    New former:
    id = 358, level = 3 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 3)(is_generic false)))t)))(scope 0)))(level 3)(is_generic false))
    Before exit:
    Current level: 3
    Region 0
    id = 346, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 347, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    Region 2
    id = 350, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false))
    id = 354, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))
    id = 349, level = 2 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false))
    id = 350, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false))
    id = 348, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false))
    id = 353, level = 2 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false))
    id = 352, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))
    id = 352, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))
    Region 3
    id = 358, level = 3 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 3)(is_generic false)))t)))(scope 0)))(level 3)(is_generic false))
    id = 357, level = 3 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 2))(scope 0)))(level 3)(is_generic false))
    Region 4
    Scope Array order:
    357,358
    Array order:
    357,358
    After exit:
    Current level: 2
    Region 0
    id = 346, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 347, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    Region 2
    id = 350, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false))
    id = 354, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))
    id = 349, level = 2 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false))
    id = 350, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false))
    id = 348, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false))
    id = 353, level = 2 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false))
    id = 352, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))
    id = 352, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))
    Region 3
    Region 4
    New variable:
    id = 359, level = 2 is_generic = false, scope = 0
    New rigid variable: 2
    id = 360, level = 2 is_generic = false, scope = 0
    New rigid variable: 3
    id = 361, level = 2 is_generic = false, scope = 0
    New former:
    id = 362, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))
    New rigid variable: 2
    id = 363, level = 2 is_generic = false, scope = 0
    New rigid variable: 3
    id = 364, level = 2 is_generic = false, scope = 0
    New former:
    id = 365, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))
    Unify: 359 365
    Unify: 362 349
    New variable:
    id = 366, level = 2 is_generic = false, scope = 0
    New variable:
    id = 367, level = 2 is_generic = false, scope = 0
    New former:
    id = 368, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))
    Unify: 359 368
    Before exit:
    Current level: 4
    Region 0
    id = 346, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 347, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    Region 2
    id = 350, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false))
    id = 359, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))
    id = 359, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))
    id = 362, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))
    id = 364, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false))
    id = 353, level = 2 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false))
    id = 363, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))
    id = 364, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false))
    id = 363, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))
    id = 359, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))
    id = 354, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))
    id = 361, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false))
    id = 362, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))
    id = 348, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false))
    id = 360, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))
    id = 352, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))
    Region 3
    Region 4
    Region 5
    Region 6
    Scope Array order:

    Array order:

    After exit:
    Current level: 3
    Region 0
    id = 346, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 347, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    Region 2
    id = 350, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false))
    id = 359, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))
    id = 359, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))
    id = 362, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))
    id = 364, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false))
    id = 353, level = 2 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false))
    id = 363, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))
    id = 364, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false))
    id = 363, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))
    id = 359, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))
    id = 354, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))
    id = 361, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false))
    id = 362, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))
    id = 348, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false))
    id = 360, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))
    id = 352, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))
    Region 3
    Region 4
    Region 5
    Region 6
    New rigid variable: 3
    id = 369, level = 3 is_generic = false, scope = 0
    New former:
    id = 370, level = 3 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 3))(scope 0)))(level 3)(is_generic false)))t)))(scope 0)))(level 3)(is_generic false))
    New rigid variable: 3
    id = 371, level = 3 is_generic = false, scope = 0
    New former:
    id = 372, level = 3 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 3))(scope 0)))(level 3)(is_generic false)))t)))(scope 0)))(level 3)(is_generic false))
    Unify: 353 372
    New rigid variable: 2
    id = 373, level = 3 is_generic = false, scope = 0
    New former:
    id = 374, level = 3 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 3)(is_generic false)))t)))(scope 0)))(level 3)(is_generic false))
    Unify: 370 374
    Before exit:
    Current level: 3
    Region 0
    id = 346, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 347, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    Region 2
    id = 350, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))((structure((desc(Structure(Constr(((structure((desc(Rigid_var 3))(scope 0)))(level 3)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false))
    id = 359, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))
    id = 359, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))
    id = 362, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))
    id = 364, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false))
    id = 353, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 3))(scope 0)))(level 3)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))
    id = 363, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))
    id = 364, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false))
    id = 363, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))
    id = 359, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))
    id = 354, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))
    id = 361, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false))
    id = 362, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))
    id = 348, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))((structure((desc(Structure(Constr(((structure((desc(Rigid_var 3))(scope 0)))(level 3)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false))
    id = 360, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))
    id = 352, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))
    Region 3
    id = 369, level = 3 is_generic = false, scope = 3
    ((structure((desc(Rigid_var 3))(scope 3)))(level 3)(is_generic false))
    id = 369, level = 3 is_generic = false, scope = 3
    ((structure((desc(Rigid_var 3))(scope 3)))(level 3)(is_generic false))
    id = 370, level = 3 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 3))(scope 3)))(level 3)(is_generic false)))t)))(scope 0)))(level 3)(is_generic false))
    id = 371, level = 3 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 3))(scope 0)))(level 3)(is_generic false))
    id = 353, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 3))(scope 0)))(level 3)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))
    id = 370, level = 3 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 3))(scope 3)))(level 3)(is_generic false)))t)))(scope 0)))(level 3)(is_generic false))
    Region 4
    Region 5
    Region 6
    Scope Array order:
    369,369,370,353,371,370
    Array order:
    353,370,371,370,369,369
    After exit:
    Current level: 2
    Region 0
    id = 346, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 347, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    Region 2
    id = 350, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))((structure((desc(Structure(Constr(((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false))
    id = 359, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))
    id = 362, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))
    id = 364, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false))
    id = 363, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))
    id = 361, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false))
    id = 348, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))((structure((desc(Structure(Constr(((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false))
    id = 360, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))
    id = 353, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))
    id = 354, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))
    id = 371, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false))
    id = 352, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))
    Region 3
    Region 4
    Region 5
    Region 6
    Before exit:
    Current level: 2
    Region 0
    id = 346, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 347, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    Region 2
    id = 350, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))((structure((desc(Structure(Constr(((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false))
    id = 359, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))
    id = 362, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))
    id = 364, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false))
    id = 363, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))
    id = 361, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false))
    id = 348, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))eq)))(scope 0)))(level 2)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))((structure((desc(Structure(Constr(((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false)))))(scope 0)))(level 2)(is_generic false))
    id = 360, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))
    id = 353, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))
    id = 354, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false))
    id = 371, level = 2 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 3))(scope 0)))(level 2)(is_generic false))
    id = 352, level = 2 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc(Rigid_var 2))(scope 0)))(level 2)(is_generic false)))t)))(scope 0)))(level 2)(is_generic false))
    Region 3
    Region 4
    Region 5
    Region 6
    Scope Array order:
    352,371,354,353,360,348,361,363,364,362,359,350
    Array order:
    352,371,354,353,360,348,361,363,364,362,359,350
    New variable:
    id = 375, level = 2 is_generic = false, scope = 0
    Unify: 354 375
    Unify: 357 354
    Unify: 360 357
    Unify: 363 360
    New variable:
    id = 376, level = 2 is_generic = false, scope = 0
    Unify: 369 376
    Unify: 361 369
    Unify: 364 361
    Unify: 371 364
    After exit:
    Current level: 1
    Region 0
    id = 346, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 347, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    Region 2
    id = 363, level = 2 is_generic = true, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic true))
    id = 371, level = 2 is_generic = true, scope = 3
    ((structure((desc Flexible_var)(scope 3)))(level 2)(is_generic true))
    Region 3
    Region 4
    Region 5
    Region 6
    New variable:
    id = 377, level = 1 is_generic = false, scope = 0
    New variable:
    id = 378, level = 1 is_generic = false, scope = 0
    New former:
    id = 379, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))eq)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 380, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))t)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 381, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))t)))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 382, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))t)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))t)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    New former:
    id = 383, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))eq)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))t)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))t)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Unify: 347 383
    Before exit:
    Current level: 1
    Region 0
    id = 346, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    id = 377, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 347, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))eq)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))t)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))t)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 381, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))t)))(scope 0)))(level 1)(is_generic false))
    id = 379, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))eq)))(scope 0)))(level 1)(is_generic false))
    id = 347, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))eq)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))t)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))t)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    id = 378, level = 1 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false))
    id = 380, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))t)))(scope 0)))(level 1)(is_generic false))
    id = 382, level = 1 is_generic = false, scope = 0
    ((structure((desc(Structure(Arrow((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))t)))(scope 0)))(level 1)(is_generic false))((structure((desc(Structure(Constr(((structure((desc Flexible_var)(scope 0)))(level 1)(is_generic false)))t)))(scope 0)))(level 1)(is_generic false)))))(scope 0)))(level 1)(is_generic false))
    Region 2
    id = 363, level = 2 is_generic = true, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic true))
    id = 371, level = 2 is_generic = true, scope = 3
    ((structure((desc Flexible_var)(scope 3)))(level 2)(is_generic true))
    Region 3
    Region 4
    Region 5
    Region 6
    Scope Array order:
    382,380,378,347,379,381,347,377
    Array order:
    382,380,378,347,379,381,347,377
    After exit:
    Current level: 0
    Region 0
    id = 346, level = 0 is_generic = false, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    id = 363, level = 2 is_generic = true, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic true))
    id = 371, level = 2 is_generic = true, scope = 3
    ((structure((desc Flexible_var)(scope 3)))(level 2)(is_generic true))
    Region 3
    Region 4
    Region 5
    Region 6
    New former:
    id = 384, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()unit)))(scope 0)))(level 0)(is_generic false))
    Unify: 346 384
    Before exit:
    Current level: 0
    Region 0
    id = 346, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()unit)))(scope 0)))(level 0)(is_generic false))
    id = 346, level = 0 is_generic = false, scope = 0
    ((structure((desc(Structure(Constr()unit)))(scope 0)))(level 0)(is_generic false))
    Region 1
    Region 2
    id = 363, level = 2 is_generic = true, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic true))
    id = 371, level = 2 is_generic = true, scope = 3
    ((structure((desc Flexible_var)(scope 3)))(level 2)(is_generic true))
    Region 3
    Region 4
    Region 5
    Region 6
    Scope Array order:
    346,346
    Array order:
    346,346
    After exit:
    Current level: -1
    Region 0
    Region 1
    Region 2
    id = 363, level = 2 is_generic = true, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 2)(is_generic true))
    id = 371, level = 2 is_generic = true, scope = 3
    ((structure((desc Flexible_var)(scope 3)))(level 2)(is_generic true))
    Region 3
    Region 4
    Region 5
    Region 6
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Constructor: unit
       └──Desc: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: α377
                         └──Type expr: Variable: α378
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: α377
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: α378
                   └──Desc: Variable: coerce
                └──Abstraction:
                   └──Variables: α378,α377
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: α377
                            └──Type expr: Variable: α378
                         └──Type expr: Arrow
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: α377
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: α378
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: α363
                               └──Type expr: Variable: α371
                            └──Desc: Variable: eq
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: α363
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: α371
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: α363
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: α371
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: α363
                                           └──Type expr: Variable: α371
                                        └──Desc: Variable
                                           └──Variable: eq
                                     └──Type expr: Constructor: eq
                                        └──Type expr: Variable: α363
                                        └──Type expr: Variable: α371
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: α363
                                                 └──Type expr: Variable: α371
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Refl
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: α363
                                                          └──Type expr: Variable: α371
                                           └──Expression:
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: α371
                                              └──Desc: Variable
                                                 └──Variable: x
          └──Expression:
             └──Type expr: Constructor: unit
             └──Desc: Constant: () |}]

let%expect_test "solve" =
  let open Constraint in
  let cst =
    let a1 = fresh () in
    let a2 = fresh () in
    forall
      [ a1; a2 ]
      (def_poly
         ~flexible_vars:[]
         ~bindings:[ "x" #= a1 ]
         ~in_:[ Var a1, Var a2 ] #=> (inst "x" a2))
  in
  print_solve_result cst;
  [%expect
    {|
    ((Forall (371 372))
     ((Def_poly ()) ((x 371))
      ((Implication (((Var 371) (Var 372)))) ((Instance x) 372))))
    Solver: bind_rigid
    Solver: bind_rigid
    New rigid variable: 4
    id = 385, level = 1 is_generic = false, scope = 0
    Before exit:
    Current level: 1
    Region 0
    Region 1
    id = 385, level = 1 is_generic = false, scope = 0
    ((structure((desc(Rigid_var 4))(scope 0)))(level 1)(is_generic false))
    Scope Array order:
    385
    Array order:
    385
    After exit:
    Current level: 0
    Region 0
    Region 1
    New rigid variable: 4
    id = 386, level = 1 is_generic = false, scope = 0
    New rigid variable: 5
    id = 387, level = 1 is_generic = false, scope = 0
    Unify: 387 386
    Before exit:
    Current level: 1
    Region 0
    Region 1
    id = 387, level = 1 is_generic = false, scope = 1
    ((structure((desc(Rigid_var 5))(scope 1)))(level 1)(is_generic false))
    id = 387, level = 1 is_generic = false, scope = 1
    ((structure((desc(Rigid_var 5))(scope 1)))(level 1)(is_generic false))
    Region 2
    Scope Array order:
    387,387
    Array order:
    387,387
    After exit:
    Current level: 0
    Region 0
    Region 1
    Region 2
    Before exit:
    Current level: 0
    Region 0
    Region 1
    Region 2
    Scope Array order:

    Array order:

    New variable:
    id = 388, level = 0 is_generic = false, scope = 0
    Unify: 385 388
    New variable:
    id = 389, level = 0 is_generic = false, scope = 0
    Unify: 387 389
    After exit:
    Current level: -1
    Region 0
    id = 387, level = 0 is_generic = true, scope = 1
    ((structure((desc Flexible_var)(scope 1)))(level 0)(is_generic true))
    id = 385, level = 0 is_generic = true, scope = 0
    ((structure((desc Flexible_var)(scope 0)))(level 0)(is_generic true))
    Region 1
    Region 2
    Constraint is true. |}]

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