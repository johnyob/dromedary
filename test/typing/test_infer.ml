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
  [%expect
    {|
    New variable:
    id = 0, level = 0 is_generic = false, scope = 0
    New former:
    id = 1, level = 0 is_generic = false, scope = 0
    (Constr()int)
    Unify: 0 1
    Before exit:
    Current level: 0
    Region 0
    id = 0, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 0, level = 0 is_generic = false, scope = 0
    (Constr()int)
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
    (Constr()bool)
    Unify: 2 3
    Before exit:
    Current level: 0
    Region 0
    id = 2, level = 0 is_generic = false, scope = 0
    (Constr()bool)
    id = 2, level = 0 is_generic = false, scope = 0
    (Constr()bool)
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
    (Constr()unit)
    Unify: 4 5
    Before exit:
    Current level: 0
    Region 0
    id = 4, level = 0 is_generic = false, scope = 0
    (Constr()unit)
    id = 4, level = 0 is_generic = false, scope = 0
    (Constr()unit)
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
    (Arrow 7f 6f)
    New variable:
    id = 9, level = 0 is_generic = false, scope = 0
    New former:
    id = 10, level = 0 is_generic = false, scope = 0
    (Arrow 9f(Arrow 7f 6f))
    New former:
    id = 11, level = 0 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 12, level = 0 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 13, level = 0 is_generic = false, scope = 0
    (Constr()bool)
    New former:
    id = 14, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()bool))
    New former:
    id = 15, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    Unify: 10 15
    New variable:
    id = 16, level = 0 is_generic = false, scope = 0
    New former:
    id = 17, level = 0 is_generic = false, scope = 0
    (Arrow 16f(Constr()int))
    New variable:
    id = 18, level = 0 is_generic = false, scope = 0
    New former:
    id = 19, level = 0 is_generic = false, scope = 0
    (Arrow 18f(Arrow 16f(Constr()int)))
    New former:
    id = 20, level = 0 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 21, level = 0 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 22, level = 0 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 23, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    New former:
    id = 24, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    Unify: 19 24
    New former:
    id = 25, level = 0 is_generic = false, scope = 0
    (Constr()int)
    Unify: 18 25
    New variable:
    id = 26, level = 0 is_generic = false, scope = 0
    New former:
    id = 27, level = 0 is_generic = false, scope = 0
    (Arrow 26f(Constr()int))
    New variable:
    id = 28, level = 0 is_generic = false, scope = 0
    New former:
    id = 29, level = 0 is_generic = false, scope = 0
    (Arrow 28f(Arrow 26f(Constr()int)))
    New former:
    id = 30, level = 0 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 31, level = 0 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 32, level = 0 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 33, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    New former:
    id = 34, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    Unify: 29 34
    New variable:
    id = 35, level = 0 is_generic = false, scope = 0
    New former:
    id = 36, level = 0 is_generic = false, scope = 0
    (Arrow 35f(Constr()int))
    New variable:
    id = 37, level = 0 is_generic = false, scope = 0
    New former:
    id = 38, level = 0 is_generic = false, scope = 0
    (Arrow 37f(Arrow 35f(Constr()int)))
    New former:
    id = 39, level = 0 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 40, level = 0 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 41, level = 0 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 42, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    New former:
    id = 43, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    Unify: 38 43
    New former:
    id = 44, level = 0 is_generic = false, scope = 0
    (Constr()int)
    Unify: 37 44
    New former:
    id = 45, level = 0 is_generic = false, scope = 0
    (Constr()int)
    Unify: 35 45
    New variable:
    id = 46, level = 0 is_generic = false, scope = 0
    New former:
    id = 47, level = 0 is_generic = false, scope = 0
    (Arrow 46f(Constr()int))
    New variable:
    id = 48, level = 0 is_generic = false, scope = 0
    New former:
    id = 49, level = 0 is_generic = false, scope = 0
    (Arrow 48f(Arrow 46f(Constr()int)))
    New former:
    id = 50, level = 0 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 51, level = 0 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 52, level = 0 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 53, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    New former:
    id = 54, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    Unify: 49 54
    New former:
    id = 55, level = 0 is_generic = false, scope = 0
    (Constr()int)
    Unify: 48 55
    New former:
    id = 56, level = 0 is_generic = false, scope = 0
    (Constr()int)
    Unify: 46 56
    New former:
    id = 57, level = 0 is_generic = false, scope = 0
    (Constr()int)
    Unify: 7 57
    Before exit:
    Current level: 0
    Region 0
    id = 38, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 29, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 35, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 46, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 7, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 37, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 46, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 9, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 10, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    id = 26, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 36, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 28, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 7, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 36, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 37, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 16, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 37, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 47, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 28, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 47, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 35, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 49, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 48, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 8, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()bool))
    id = 38, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 46, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 27, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 6, level = 0 is_generic = false, scope = 0
    (Constr()bool)
    id = 48, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 49, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 26, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 35, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 17, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 48, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 18, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 19, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
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
    (Arrow 59f 60f)
    Unify: 58 61
    Unify: 60 59
    Before exit:
    Current level: 0
    Region 0
    id = 60, level = 0 is_generic = false, scope = 0
    60f
    id = 58, level = 0 is_generic = false, scope = 0
    (Arrow 60f 60f)
    id = 60, level = 0 is_generic = false, scope = 0
    60f
    id = 58, level = 0 is_generic = false, scope = 0
    (Arrow 60f 60f)
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
    (Arrow 63f 64f)
    Unify: 62 65
    New variable:
    id = 66, level = 0 is_generic = false, scope = 0
    New variable:
    id = 67, level = 0 is_generic = false, scope = 0
    New former:
    id = 68, level = 0 is_generic = false, scope = 0
    (Arrow 66f 67f)
    Unify: 64 68
    New variable:
    id = 69, level = 0 is_generic = false, scope = 0
    New variable:
    id = 70, level = 0 is_generic = false, scope = 0
    New former:
    id = 71, level = 0 is_generic = false, scope = 0
    (Arrow 69f 70f)
    Unify: 67 71
    New variable:
    id = 72, level = 0 is_generic = false, scope = 0
    New former:
    id = 73, level = 0 is_generic = false, scope = 0
    (Arrow 72f 70f)
    Unify: 73 63
    New variable:
    id = 74, level = 0 is_generic = false, scope = 0
    New variable:
    id = 75, level = 0 is_generic = false, scope = 0
    New former:
    id = 76, level = 0 is_generic = false, scope = 0
    (Tuple(74f 75f))
    Unify: 72 76
    Unify: 74 66
    Unify: 75 69
    Before exit:
    Current level: 0
    Region 0
    id = 67, level = 0 is_generic = false, scope = 0
    (Arrow 75f 70f)
    id = 72, level = 0 is_generic = false, scope = 0
    (Tuple(74f 75f))
    id = 64, level = 0 is_generic = false, scope = 0
    (Arrow 74f(Arrow 75f 70f))
    id = 72, level = 0 is_generic = false, scope = 0
    (Tuple(74f 75f))
    id = 75, level = 0 is_generic = false, scope = 0
    75f
    id = 62, level = 0 is_generic = false, scope = 0
    (Arrow(Arrow(Tuple(74f 75f))70f)(Arrow 74f(Arrow 75f 70f)))
    id = 75, level = 0 is_generic = false, scope = 0
    75f
    id = 74, level = 0 is_generic = false, scope = 0
    74f
    id = 73, level = 0 is_generic = false, scope = 0
    (Arrow(Tuple(74f 75f))70f)
    id = 74, level = 0 is_generic = false, scope = 0
    74f
    id = 70, level = 0 is_generic = false, scope = 0
    70f
    id = 67, level = 0 is_generic = false, scope = 0
    (Arrow 75f 70f)
    id = 73, level = 0 is_generic = false, scope = 0
    (Arrow(Tuple(74f 75f))70f)
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
    (Arrow 78f 79f)
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
    (Arrow 81f 82f)
    Unify: 79 85
    New former:
    id = 86, level = 0 is_generic = false, scope = 0
    (Tuple(84f 83f))
    Unify: 81 86
    New variable:
    id = 87, level = 0 is_generic = false, scope = 0
    New former:
    id = 88, level = 0 is_generic = false, scope = 0
    (Arrow 87f 82f)
    New variable:
    id = 89, level = 0 is_generic = false, scope = 0
    New former:
    id = 90, level = 0 is_generic = false, scope = 0
    (Arrow 89f(Arrow 87f 82f))
    Unify: 90 78
    Unify: 89 84
    Unify: 87 83
    Before exit:
    Current level: 0
    Region 0
    id = 81, level = 0 is_generic = false, scope = 0
    (Tuple(89f 87f))
    id = 88, level = 0 is_generic = false, scope = 0
    (Arrow 87f 82f)
    id = 87, level = 0 is_generic = false, scope = 0
    87f
    id = 89, level = 0 is_generic = false, scope = 0
    89f
    id = 77, level = 0 is_generic = false, scope = 0
    (Arrow(Arrow 89f(Arrow 87f 82f))(Arrow(Tuple(89f 87f))82f))
    id = 87, level = 0 is_generic = false, scope = 0
    87f
    id = 79, level = 0 is_generic = false, scope = 0
    (Arrow(Tuple(89f 87f))82f)
    id = 81, level = 0 is_generic = false, scope = 0
    (Tuple(89f 87f))
    id = 90, level = 0 is_generic = false, scope = 0
    (Arrow 89f(Arrow 87f 82f))
    id = 90, level = 0 is_generic = false, scope = 0
    (Arrow 89f(Arrow 87f 82f))
    id = 89, level = 0 is_generic = false, scope = 0
    89f
    id = 82, level = 0 is_generic = false, scope = 0
    82f
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
    (Arrow 92f 93f)
    Unify: 91 94
    New variable:
    id = 95, level = 0 is_generic = false, scope = 0
    New variable:
    id = 96, level = 0 is_generic = false, scope = 0
    New former:
    id = 97, level = 0 is_generic = false, scope = 0
    (Arrow 95f 96f)
    Unify: 93 97
    New variable:
    id = 98, level = 0 is_generic = false, scope = 0
    New variable:
    id = 99, level = 0 is_generic = false, scope = 0
    New former:
    id = 100, level = 0 is_generic = false, scope = 0
    (Arrow 98f 99f)
    Unify: 96 100
    New variable:
    id = 101, level = 0 is_generic = false, scope = 0
    New former:
    id = 102, level = 0 is_generic = false, scope = 0
    (Arrow 101f 99f)
    Unify: 102 92
    New variable:
    id = 103, level = 0 is_generic = false, scope = 0
    New former:
    id = 104, level = 0 is_generic = false, scope = 0
    (Arrow 103f 101f)
    Unify: 104 95
    Unify: 103 98
    Before exit:
    Current level: 0
    Region 0
    id = 93, level = 0 is_generic = false, scope = 0
    (Arrow(Arrow 103f 101f)(Arrow 103f 99f))
    id = 96, level = 0 is_generic = false, scope = 0
    (Arrow 103f 99f)
    id = 99, level = 0 is_generic = false, scope = 0
    99f
    id = 102, level = 0 is_generic = false, scope = 0
    (Arrow 101f 99f)
    id = 103, level = 0 is_generic = false, scope = 0
    103f
    id = 101, level = 0 is_generic = false, scope = 0
    101f
    id = 91, level = 0 is_generic = false, scope = 0
    (Arrow(Arrow 101f 99f)(Arrow(Arrow 103f 101f)(Arrow 103f 99f)))
    id = 103, level = 0 is_generic = false, scope = 0
    103f
    id = 104, level = 0 is_generic = false, scope = 0
    (Arrow 103f 101f)
    id = 102, level = 0 is_generic = false, scope = 0
    (Arrow 101f 99f)
    id = 96, level = 0 is_generic = false, scope = 0
    (Arrow 103f 99f)
    id = 104, level = 0 is_generic = false, scope = 0
    (Arrow 103f 101f)
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
    (Arrow 106f 107f)
    Unify: 105 110
    New former:
    id = 111, level = 0 is_generic = false, scope = 0
    (Tuple(109f 108f))
    Unify: 106 111
    Unify: 107 109
    Before exit:
    Current level: 0
    Region 0
    id = 105, level = 0 is_generic = false, scope = 0
    (Arrow(Tuple(107f 108f))107f)
    id = 107, level = 0 is_generic = false, scope = 0
    107f
    id = 106, level = 0 is_generic = false, scope = 0
    (Tuple(107f 108f))
    id = 106, level = 0 is_generic = false, scope = 0
    (Tuple(107f 108f))
    id = 107, level = 0 is_generic = false, scope = 0
    107f
    id = 108, level = 0 is_generic = false, scope = 0
    108f
    id = 105, level = 0 is_generic = false, scope = 0
    (Arrow(Tuple(107f 108f))107f)
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
    (Arrow 113f 114f)
    Unify: 112 117
    New former:
    id = 118, level = 0 is_generic = false, scope = 0
    (Tuple(116f 115f))
    Unify: 113 118
    Unify: 114 115
    Before exit:
    Current level: 0
    Region 0
    id = 113, level = 0 is_generic = false, scope = 0
    (Tuple(116f 114f))
    id = 114, level = 0 is_generic = false, scope = 0
    114f
    id = 114, level = 0 is_generic = false, scope = 0
    114f
    id = 113, level = 0 is_generic = false, scope = 0
    (Tuple(116f 114f))
    id = 112, level = 0 is_generic = false, scope = 0
    (Arrow(Tuple(116f 114f))114f)
    id = 116, level = 0 is_generic = false, scope = 0
    116f
    id = 112, level = 0 is_generic = false, scope = 0
    (Arrow(Tuple(116f 114f))114f)
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
    (Constr(122f)list)
    New former:
    id = 124, level = 0 is_generic = false, scope = 0
    (Tuple(122f(Constr(122f)list)))
    New former:
    id = 125, level = 0 is_generic = false, scope = 0
    (Constr(122f)list)
    New variable:
    id = 126, level = 0 is_generic = false, scope = 0
    New variable:
    id = 127, level = 0 is_generic = false, scope = 0
    New former:
    id = 128, level = 0 is_generic = false, scope = 0
    (Arrow 120f 121f)
    Unify: 119 128
    Unify: 120 125
    New former:
    id = 129, level = 0 is_generic = false, scope = 0
    (Tuple(127f 126f))
    Unify: 124 129
    Unify: 121 122
    Before exit:
    Current level: 0
    Region 0
    id = 120, level = 0 is_generic = false, scope = 0
    (Constr(121f)list)
    id = 119, level = 0 is_generic = false, scope = 0
    (Arrow(Constr(121f)list)121f)
    id = 121, level = 0 is_generic = false, scope = 0
    121f
    id = 123, level = 0 is_generic = false, scope = 0
    (Constr(121f)list)
    id = 123, level = 0 is_generic = false, scope = 0
    (Constr(121f)list)
    id = 120, level = 0 is_generic = false, scope = 0
    (Constr(121f)list)
    id = 121, level = 0 is_generic = false, scope = 0
    121f
    id = 119, level = 0 is_generic = false, scope = 0
    (Arrow(Constr(121f)list)121f)
    id = 124, level = 0 is_generic = false, scope = 0
    (Tuple(121f(Constr(121f)list)))
    id = 124, level = 0 is_generic = false, scope = 0
    (Tuple(121f(Constr(121f)list)))
    id = 121, level = 0 is_generic = false, scope = 0
    121f
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
    (Arrow 132f 133f)
    Unify: 130 134
    Unify: 132 131
    Unify: 133 132
    Before exit:
    Current level: 0
    Region 0
    id = 133, level = 0 is_generic = false, scope = 0
    133f
    id = 130, level = 0 is_generic = false, scope = 0
    (Arrow 133f 133f)
    id = 130, level = 0 is_generic = false, scope = 0
    (Arrow 133f 133f)
    id = 133, level = 0 is_generic = false, scope = 0
    133f
    id = 133, level = 0 is_generic = false, scope = 0
    133f
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
    (Arrow 137f 138f)
    Unify: 136 139
    New rigid variable: 0
    id = 140, level = 1 is_generic = false, scope = 0
    Unify: 137 140
    New rigid variable: 0
    id = 141, level = 1 is_generic = false, scope = 0
    New variable:
    id = 142, level = 1 is_generic = false, scope = 0
    Unify: 138 142
    Before exit:
    Current level: 1
    Region 0
    id = 135, level = 0 is_generic = false, scope = 0
    135f
    Region 1
    id = 136, level = 1 is_generic = false, scope = 0
    (Arrow 0r 0r)
    id = 138, level = 1 is_generic = false, scope = 0
    0r
    id = 137, level = 1 is_generic = false, scope = 0
    0r
    id = 137, level = 1 is_generic = false, scope = 0
    0r
    id = 141, level = 1 is_generic = false, scope = 0
    0r
    id = 138, level = 1 is_generic = false, scope = 0
    0r
    Scope Array order:
    138,141,137,137,138,136
    Array order:
    138,141,137,137,138,136
    New variable:
    id = 143, level = 1 is_generic = false, scope = 0
    After exit:
    Current level: 0
    Region 0
    id = 135, level = 0 is_generic = false, scope = 0
    135f
    Region 1
    New variable:
    id = 144, level = 0 is_generic = false, scope = 0
    New variable:
    id = 145, level = 0 is_generic = false, scope = 0
    Unify: 135 144
    Before exit:
    Current level: 0
    Region 0
    id = 135, level = 0 is_generic = false, scope = 0
    (Arrow 145f 145f)
    id = 135, level = 0 is_generic = false, scope = 0
    (Arrow 145f 145f)
    id = 145, level = 0 is_generic = false, scope = 0
    145f
    Region 1
    Scope Array order:
    145,135,135
    Array order:
    145,135,135
    After exit:
    Current level: -1
    Region 0
    Region 1
    Variables: α145
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Variable: α145
          └──Type expr: Variable: α145
       └──Desc: Function
          └──Pattern:
             └──Type expr: Variable: α143
             └──Desc: Variable: x
          └──Expression:
             └──Type expr: Variable: α143
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
    (Arrow 148f 149f)
    Unify: 146 150
    Unify: 148 147
    New variable:
    id = 151, level = 0 is_generic = false, scope = 0
    New former:
    id = 152, level = 0 is_generic = false, scope = 0
    (Arrow 151f 149f)
    New variable:
    id = 153, level = 0 is_generic = false, scope = 0
    New former:
    id = 154, level = 0 is_generic = false, scope = 0
    (Arrow 153f(Arrow 151f 149f))
    New former:
    id = 155, level = 0 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 156, level = 0 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 157, level = 0 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 158, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    New former:
    id = 159, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    Unify: 154 159
    Unify: 153 148
    New former:
    id = 160, level = 0 is_generic = false, scope = 0
    (Constr()int)
    Unify: 151 160
    Before exit:
    Current level: 0
    Region 0
    id = 153, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 146, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 151, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 152, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 154, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 153, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 153, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 152, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 151, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 149, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 149, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 154, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 151, level = 0 is_generic = false, scope = 0
    (Constr()int)
    Scope Array order:
    151,154,149,149,151,152,153,153,154,152,151,146,153
    Array order:
    151,154,149,149,151,152,153,153,154,152,151,146,153
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
    (Arrow 163f 164f)
    Unify: 162 165
    New rigid variable: 1
    id = 166, level = 1 is_generic = false, scope = 0
    Unify: 163 166
    New rigid variable: 1
    id = 167, level = 1 is_generic = false, scope = 0
    New variable:
    id = 168, level = 1 is_generic = false, scope = 0
    New former:
    id = 169, level = 1 is_generic = false, scope = 0
    (Arrow 168f 164f)
    New variable:
    id = 170, level = 1 is_generic = false, scope = 0
    New former:
    id = 171, level = 1 is_generic = false, scope = 0
    (Arrow 170f(Arrow 168f 164f))
    New former:
    id = 172, level = 1 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 173, level = 1 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 174, level = 1 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 175, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    New former:
    id = 176, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    Unify: 171 176
    New variable:
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
    (Arrow 180f 181f)
    Unify: 179 182
    Unify: 181 180
    Before exit:
    Current level: 1
    Region 0
    id = 178, level = 0 is_generic = false, scope = 0
    178f
    Region 1
    id = 181, level = 1 is_generic = false, scope = 0
    181f
    id = 179, level = 1 is_generic = false, scope = 0
    (Arrow 181f 181f)
    id = 181, level = 1 is_generic = false, scope = 0
    181f
    id = 179, level = 1 is_generic = false, scope = 0
    (Arrow 181f 181f)
    Scope Array order:
    179,181,179,181
    Array order:
    179,181,179,181
    After exit:
    Current level: 0
    Region 0
    id = 178, level = 0 is_generic = false, scope = 0
    178f
    Region 1
    New variable:
    id = 183, level = 0 is_generic = false, scope = 0
    New former:
    id = 184, level = 0 is_generic = false, scope = 0
    (Arrow 183f 178f)
    New variable:
    id = 185, level = 0 is_generic = false, scope = 0
    New former:
    id = 186, level = 0 is_generic = false, scope = 0
    (Arrow 185f(Arrow 183f 178f))
    New variable:
    id = 187, level = 0 is_generic = false, scope = 0
    New variable:
    id = 188, level = 0 is_generic = false, scope = 0
    Unify: 186 187
    New variable:
    id = 189, level = 0 is_generic = false, scope = 0
    New variable:
    id = 190, level = 0 is_generic = false, scope = 0
    Unify: 184 189
    New former:
    id = 191, level = 0 is_generic = false, scope = 0
    (Constr()unit)
    Unify: 178 191
    Before exit:
    Current level: 0
    Region 0
    id = 178, level = 0 is_generic = false, scope = 0
    (Constr()unit)
    id = 178, level = 0 is_generic = false, scope = 0
    (Constr()unit)
    id = 186, level = 0 is_generic = false, scope = 0
    (Arrow(Arrow(Constr()unit)(Constr()unit))(Arrow(Constr()unit)(Constr()unit)))
    id = 184, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()unit)(Constr()unit))
    id = 178, level = 0 is_generic = false, scope = 0
    (Constr()unit)
    id = 184, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()unit)(Constr()unit))
    id = 178, level = 0 is_generic = false, scope = 0
    (Constr()unit)
    Region 1
    Scope Array order:
    178,184,178,184,186,178,178
    Array order:
    178,184,178,184,186,178,178
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
    (Arrow 194f 195f)
    Unify: 193 196
    New variable:
    id = 197, level = 1 is_generic = false, scope = 0
    New variable:
    id = 198, level = 1 is_generic = false, scope = 0
    New former:
    id = 199, level = 1 is_generic = false, scope = 0
    (Arrow 197f 198f)
    Unify: 195 199
    New variable:
    id = 200, level = 1 is_generic = false, scope = 0
    Unify: 200 197
    New variable:
    id = 201, level = 1 is_generic = false, scope = 0
    New former:
    id = 202, level = 1 is_generic = false, scope = 0
    (Constr(201f)list)
    Unify: 200 202
    New variable:
    id = 203, level = 1 is_generic = false, scope = 0
    New former:
    id = 204, level = 1 is_generic = false, scope = 0
    (Constr(203f)list)
    Unify: 198 204
    New variable:
    id = 205, level = 1 is_generic = false, scope = 0
    New former:
    id = 206, level = 1 is_generic = false, scope = 0
    (Constr(205f)list)
    New former:
    id = 207, level = 1 is_generic = false, scope = 0
    (Tuple(205f(Constr(205f)list)))
    New former:
    id = 208, level = 1 is_generic = false, scope = 0
    (Constr(205f)list)
    New variable:
    id = 209, level = 1 is_generic = false, scope = 0
    New variable:
    id = 210, level = 1 is_generic = false, scope = 0
    Unify: 200 208
    New former:
    id = 211, level = 1 is_generic = false, scope = 0
    (Tuple(210f 209f))
    Unify: 207 211
    New variable:
    id = 212, level = 1 is_generic = false, scope = 0
    New former:
    id = 213, level = 1 is_generic = false, scope = 0
    (Constr(212f)list)
    New former:
    id = 214, level = 1 is_generic = false, scope = 0
    (Tuple(212f(Constr(212f)list)))
    New former:
    id = 215, level = 1 is_generic = false, scope = 0
    (Constr(212f)list)
    Unify: 198 215
    New variable:
    id = 216, level = 1 is_generic = false, scope = 0
    New variable:
    id = 217, level = 1 is_generic = false, scope = 0
    New former:
    id = 218, level = 1 is_generic = false, scope = 0
    (Tuple(216f 217f))
    Unify: 214 218
    New variable:
    id = 219, level = 1 is_generic = false, scope = 0
    New former:
    id = 220, level = 1 is_generic = false, scope = 0
    (Arrow 219f 203f)
    Unify: 220 194
    Unify: 219 201
    New variable:
    id = 221, level = 1 is_generic = false, scope = 0
    New former:
    id = 222, level = 1 is_generic = false, scope = 0
    (Arrow 221f(Constr(203f)list))
    New variable:
    id = 223, level = 1 is_generic = false, scope = 0
    New former:
    id = 224, level = 1 is_generic = false, scope = 0
    (Arrow 223f(Arrow 221f(Constr(203f)list)))
    New variable:
    id = 225, level = 1 is_generic = false, scope = 0
    New variable:
    id = 226, level = 1 is_generic = false, scope = 0
    New variable:
    id = 227, level = 1 is_generic = false, scope = 0
    New variable:
    id = 228, level = 1 is_generic = false, scope = 0
    New variable:
    id = 229, level = 1 is_generic = false, scope = 0
    Unify: 224 225
    New variable:
    id = 230, level = 1 is_generic = false, scope = 0
    Unify: 223 230
    New variable:
    id = 231, level = 1 is_generic = false, scope = 0
    Unify: 221 231
    Before exit:
    Current level: 1
    Region 0
    id = 192, level = 0 is_generic = false, scope = 0
    192f
    Region 1
    id = 195, level = 1 is_generic = false, scope = 0
    (Arrow(Constr(219f)list)(Constr(203f)list))
    id = 203, level = 1 is_generic = false, scope = 0
    203f
    id = 219, level = 1 is_generic = false, scope = 0
    219f
    id = 207, level = 1 is_generic = false, scope = 0
    (Tuple(219f(Constr(219f)list)))
    id = 220, level = 1 is_generic = false, scope = 0
    (Arrow 219f 203f)
    id = 203, level = 1 is_generic = false, scope = 0
    203f
    id = 224, level = 1 is_generic = false, scope = 0
    (Arrow(Arrow 219f 203f)(Arrow(Constr(219f)list)(Constr(203f)list)))
    id = 213, level = 1 is_generic = false, scope = 0
    (Constr(203f)list)
    id = 224, level = 1 is_generic = false, scope = 0
    (Arrow(Arrow 219f 203f)(Arrow(Constr(219f)list)(Constr(203f)list)))
    id = 203, level = 1 is_generic = false, scope = 0
    203f
    id = 214, level = 1 is_generic = false, scope = 0
    (Tuple(203f(Constr(203f)list)))
    id = 213, level = 1 is_generic = false, scope = 0
    (Constr(203f)list)
    id = 220, level = 1 is_generic = false, scope = 0
    (Arrow 219f 203f)
    id = 198, level = 1 is_generic = false, scope = 0
    (Constr(203f)list)
    id = 221, level = 1 is_generic = false, scope = 0
    (Constr(219f)list)
    id = 213, level = 1 is_generic = false, scope = 0
    (Constr(203f)list)
    id = 221, level = 1 is_generic = false, scope = 0
    (Constr(219f)list)
    id = 223, level = 1 is_generic = false, scope = 0
    (Arrow 219f 203f)
    id = 206, level = 1 is_generic = false, scope = 0
    (Constr(219f)list)
    id = 223, level = 1 is_generic = false, scope = 0
    (Arrow 219f 203f)
    id = 193, level = 1 is_generic = false, scope = 0
    (Arrow(Arrow 219f 203f)(Arrow(Constr(219f)list)(Constr(203f)list)))
    id = 219, level = 1 is_generic = false, scope = 0
    219f
    id = 200, level = 1 is_generic = false, scope = 0
    (Constr(219f)list)
    id = 214, level = 1 is_generic = false, scope = 0
    (Tuple(203f(Constr(203f)list)))
    id = 223, level = 1 is_generic = false, scope = 0
    (Arrow 219f 203f)
    id = 221, level = 1 is_generic = false, scope = 0
    (Constr(219f)list)
    id = 222, level = 1 is_generic = false, scope = 0
    (Arrow(Constr(219f)list)(Constr(203f)list))
    id = 198, level = 1 is_generic = false, scope = 0
    (Constr(203f)list)
    id = 222, level = 1 is_generic = false, scope = 0
    (Arrow(Constr(219f)list)(Constr(203f)list))
    Scope Array order:
    222,198,222,221,223,214,200,219,193,223,206,223,221,213,221,198,220,213,214,203,224,213,224,203,220,207,219,203,195
    Array order:
    222,198,222,221,223,214,200,219,193,223,206,223,221,213,221,198,220,213,214,203,224,213,224,203,220,207,219,203,195
    After exit:
    Current level: 0
    Region 0
    id = 192, level = 0 is_generic = false, scope = 0
    192f
    Region 1
    New variable:
    id = 232, level = 1 is_generic = false, scope = 0
    New variable:
    id = 233, level = 1 is_generic = false, scope = 0
    New variable:
    id = 234, level = 1 is_generic = false, scope = 0
    New former:
    id = 235, level = 1 is_generic = false, scope = 0
    (Arrow 233f 234f)
    Unify: 232 235
    New variable:
    id = 236, level = 1 is_generic = false, scope = 0
    New former:
    id = 237, level = 1 is_generic = false, scope = 0
    (Arrow 236f 234f)
    New variable:
    id = 238, level = 1 is_generic = false, scope = 0
    New former:
    id = 239, level = 1 is_generic = false, scope = 0
    (Arrow 238f(Arrow 236f 234f))
    New former:
    id = 240, level = 1 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 241, level = 1 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 242, level = 1 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 243, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    New former:
    id = 244, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    Unify: 239 244
    Unify: 238 233
    New former:
    id = 245, level = 1 is_generic = false, scope = 0
    (Constr()int)
    Unify: 236 245
    Before exit:
    Current level: 1
    Region 0
    id = 192, level = 0 is_generic = false, scope = 0
    192f
    Region 1
    id = 232, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 238, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 236, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 232, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 237, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 238, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 237, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 236, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 239, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 234, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 236, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 238, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 234, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 239, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    Region 2
    Scope Array order:
    239,234,238,236,234,239,236,237,238,237,232,236,238,232
    Array order:
    239,234,238,236,234,239,236,237,238,237,232,236,238,232
    After exit:
    Current level: 0
    Region 0
    id = 192, level = 0 is_generic = false, scope = 0
    192f
    id = 236, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 238, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 232, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 237, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 234, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 239, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    Region 1
    Region 2
    New variable:
    id = 246, level = 0 is_generic = false, scope = 0
    New former:
    id = 247, level = 0 is_generic = false, scope = 0
    (Arrow 246f 192f)
    New variable:
    id = 248, level = 0 is_generic = false, scope = 0
    New former:
    id = 249, level = 0 is_generic = false, scope = 0
    (Arrow 248f(Arrow 246f 192f))
    New variable:
    id = 250, level = 0 is_generic = false, scope = 0
    New variable:
    id = 251, level = 0 is_generic = false, scope = 0
    New variable:
    id = 252, level = 0 is_generic = false, scope = 0
    New variable:
    id = 253, level = 0 is_generic = false, scope = 0
    New variable:
    id = 254, level = 0 is_generic = false, scope = 0
    New variable:
    id = 255, level = 0 is_generic = false, scope = 0
    New variable:
    id = 256, level = 0 is_generic = false, scope = 0
    Unify: 249 250
    New variable:
    id = 257, level = 0 is_generic = false, scope = 0
    New variable:
    id = 258, level = 0 is_generic = false, scope = 0
    New variable:
    id = 259, level = 0 is_generic = false, scope = 0
    Unify: 248 257
    New variable:
    id = 260, level = 0 is_generic = false, scope = 0
    New former:
    id = 261, level = 0 is_generic = false, scope = 0
    (Constr(260f)list)
    Unify: 246 261
    Before exit:
    Current level: 0
    Region 0
    id = 253, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 192, level = 0 is_generic = false, scope = 0
    (Constr((Constr()int))list)
    id = 238, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 246, level = 0 is_generic = false, scope = 0
    (Constr((Constr()int))list)
    id = 248, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 246, level = 0 is_generic = false, scope = 0
    (Constr((Constr()int))list)
    id = 247, level = 0 is_generic = false, scope = 0
    (Arrow(Constr((Constr()int))list)(Constr((Constr()int))list))
    id = 247, level = 0 is_generic = false, scope = 0
    (Arrow(Constr((Constr()int))list)(Constr((Constr()int))list))
    id = 192, level = 0 is_generic = false, scope = 0
    (Constr((Constr()int))list)
    id = 253, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 232, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 237, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 248, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 248, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 252, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 246, level = 0 is_generic = false, scope = 0
    (Constr((Constr()int))list)
    id = 249, level = 0 is_generic = false, scope = 0
    (Arrow(Arrow(Constr()int)(Constr()int))(Arrow(Constr((Constr()int))list)(Constr((Constr()int))list)))
    id = 252, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 236, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 252, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 234, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 239, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 249, level = 0 is_generic = false, scope = 0
    (Arrow(Arrow(Constr()int)(Constr()int))(Arrow(Constr((Constr()int))list)(Constr((Constr()int))list)))
    Region 1
    Region 2
    Scope Array order:
    249,239,234,252,236,252,249,246,252,248,248,237,232,253,192,247,247,246,248,246,238,192,253
    Array order:
    249,239,234,252,236,252,249,246,252,248,248,237,232,253,192,247,247,246,248,246,238,192,253
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
    id = 262, level = 0 is_generic = false, scope = 0
    New variable:
    id = 263, level = 1 is_generic = false, scope = 0
    New variable:
    id = 264, level = 1 is_generic = false, scope = 0
    New variable:
    id = 265, level = 1 is_generic = false, scope = 0
    New variable:
    id = 266, level = 1 is_generic = false, scope = 0
    New former:
    id = 267, level = 1 is_generic = false, scope = 0
    (Arrow 265f 266f)
    Unify: 263 267
    Unify: 266 265
    New variable:
    id = 268, level = 1 is_generic = false, scope = 0
    New variable:
    id = 269, level = 1 is_generic = false, scope = 0
    New former:
    id = 270, level = 1 is_generic = false, scope = 0
    (Arrow 268f 269f)
    Unify: 264 270
    New variable:
    id = 271, level = 1 is_generic = false, scope = 0
    New former:
    id = 272, level = 1 is_generic = false, scope = 0
    (Arrow 271f 269f)
    New variable:
    id = 273, level = 1 is_generic = false, scope = 0
    Unify: 272 273
    New former:
    id = 274, level = 1 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 275, level = 1 is_generic = false, scope = 0
    (Constr()int)
    Unify: 269 275
    Unify: 274 268
    Before exit:
    Current level: 1
    Region 0
    id = 262, level = 0 is_generic = false, scope = 0
    262f
    Region 1
    id = 269, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 269, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 263, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 272, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 274, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 269, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 272, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 264, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 274, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 269, level = 1 is_generic = false, scope = 0
    (Constr()int)
    Scope Array order:
    269,274,264,272,269,274,272,263,269,269
    Array order:
    269,274,264,272,269,274,272,263,269,269
    After exit:
    Current level: 0
    Region 0
    id = 269, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 264, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 263, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 272, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 274, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 262, level = 0 is_generic = false, scope = 0
    262f
    Region 1
    New variable:
    id = 276, level = 0 is_generic = false, scope = 0
    New variable:
    id = 277, level = 0 is_generic = false, scope = 0
    Unify: 262 276
    Before exit:
    Current level: 0
    Region 0
    id = 269, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 262, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 277, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 264, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 263, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 272, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 274, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 262, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    Region 1
    Scope Array order:
    262,274,272,263,264,277,262,269
    Array order:
    262,274,272,263,264,277,262,269
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
  [%expect
    {|
    New variable:
    id = 278, level = 0 is_generic = false, scope = 0
    New variable:
    id = 279, level = 1 is_generic = false, scope = 0
    New variable:
    id = 280, level = 1 is_generic = false, scope = 0
    New variable:
    id = 281, level = 1 is_generic = false, scope = 0
    New variable:
    id = 282, level = 1 is_generic = false, scope = 0
    New former:
    id = 283, level = 1 is_generic = false, scope = 0
    (Arrow 281f 282f)
    Unify: 279 283
    New former:
    id = 284, level = 1 is_generic = false, scope = 0
    (Constr()bool)
    New variable:
    id = 285, level = 1 is_generic = false, scope = 0
    New former:
    id = 286, level = 1 is_generic = false, scope = 0
    (Arrow 285f(Constr()bool))
    New variable:
    id = 287, level = 1 is_generic = false, scope = 0
    New former:
    id = 288, level = 1 is_generic = false, scope = 0
    (Arrow 287f(Arrow 285f(Constr()bool)))
    New former:
    id = 289, level = 1 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 290, level = 1 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 291, level = 1 is_generic = false, scope = 0
    (Constr()bool)
    New former:
    id = 292, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()bool))
    New former:
    id = 293, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    Unify: 288 293
    Unify: 287 281
    New former:
    id = 294, level = 1 is_generic = false, scope = 0
    (Constr()int)
    Unify: 285 294
    New former:
    id = 295, level = 1 is_generic = false, scope = 0
    (Constr()bool)
    Unify: 282 295
    New variable:
    id = 296, level = 1 is_generic = false, scope = 0
    New former:
    id = 297, level = 1 is_generic = false, scope = 0
    (Arrow 296f(Constr()bool))
    Unify: 297 280
    New variable:
    id = 298, level = 1 is_generic = false, scope = 0
    New former:
    id = 299, level = 1 is_generic = false, scope = 0
    (Arrow 298f 296f)
    New variable:
    id = 300, level = 1 is_generic = false, scope = 0
    New former:
    id = 301, level = 1 is_generic = false, scope = 0
    (Arrow 300f(Arrow 298f 296f))
    New former:
    id = 302, level = 1 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 303, level = 1 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 304, level = 1 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 305, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    New former:
    id = 306, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    Unify: 301 306
    New variable:
    id = 307, level = 1 is_generic = false, scope = 0
    Unify: 300 307
    New former:
    id = 308, level = 1 is_generic = false, scope = 0
    (Constr()int)
    Unify: 298 308
    New variable:
    id = 309, level = 1 is_generic = false, scope = 0
    New variable:
    id = 310, level = 1 is_generic = false, scope = 0
    New former:
    id = 311, level = 1 is_generic = false, scope = 0
    (Arrow 309f 310f)
    Unify: 297 311
    New former:
    id = 312, level = 1 is_generic = false, scope = 0
    (Constr()bool)
    New variable:
    id = 313, level = 1 is_generic = false, scope = 0
    New former:
    id = 314, level = 1 is_generic = false, scope = 0
    (Arrow 313f(Constr()bool))
    New variable:
    id = 315, level = 1 is_generic = false, scope = 0
    New former:
    id = 316, level = 1 is_generic = false, scope = 0
    (Arrow 315f(Arrow 313f(Constr()bool)))
    New former:
    id = 317, level = 1 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 318, level = 1 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 319, level = 1 is_generic = false, scope = 0
    (Constr()bool)
    New former:
    id = 320, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()bool))
    New former:
    id = 321, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    Unify: 316 321
    New variable:
    id = 322, level = 1 is_generic = false, scope = 0
    Unify: 315 322
    New former:
    id = 323, level = 1 is_generic = false, scope = 0
    (Constr()int)
    Unify: 313 323
    New former:
    id = 324, level = 1 is_generic = false, scope = 0
    (Constr()bool)
    Unify: 282 324
    New variable:
    id = 325, level = 1 is_generic = false, scope = 0
    New former:
    id = 326, level = 1 is_generic = false, scope = 0
    (Arrow 325f(Constr()bool))
    New variable:
    id = 327, level = 1 is_generic = false, scope = 0
    New variable:
    id = 328, level = 1 is_generic = false, scope = 0
    New variable:
    id = 329, level = 1 is_generic = false, scope = 0
    Unify: 326 327
    New variable:
    id = 330, level = 1 is_generic = false, scope = 0
    New former:
    id = 331, level = 1 is_generic = false, scope = 0
    (Arrow 330f(Constr()int))
    New variable:
    id = 332, level = 1 is_generic = false, scope = 0
    New former:
    id = 333, level = 1 is_generic = false, scope = 0
    (Arrow 332f(Arrow 330f(Constr()int)))
    New former:
    id = 334, level = 1 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 335, level = 1 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 336, level = 1 is_generic = false, scope = 0
    (Constr()int)
    New former:
    id = 337, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    New former:
    id = 338, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    Unify: 333 338
    New variable:
    id = 339, level = 1 is_generic = false, scope = 0
    Unify: 332 339
    New former:
    id = 340, level = 1 is_generic = false, scope = 0
    (Constr()int)
    Unify: 330 340
    Before exit:
    Current level: 1
    Region 0
    id = 278, level = 0 is_generic = false, scope = 0
    278f
    Region 1
    id = 315, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 314, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()bool))
    id = 282, level = 1 is_generic = false, scope = 0
    (Constr()bool)
    id = 297, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()bool))
    id = 312, level = 1 is_generic = false, scope = 0
    (Constr()bool)
    id = 325, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 330, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 279, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()bool))
    id = 296, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 282, level = 1 is_generic = false, scope = 0
    (Constr()bool)
    id = 287, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 299, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 313, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 326, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()bool))
    id = 333, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 331, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 282, level = 1 is_generic = false, scope = 0
    (Constr()bool)
    id = 332, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 285, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 325, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 286, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()bool))
    id = 298, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 288, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    id = 315, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 330, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 330, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 312, level = 1 is_generic = false, scope = 0
    (Constr()bool)
    id = 332, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 300, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 314, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()bool))
    id = 316, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    id = 284, level = 1 is_generic = false, scope = 0
    (Constr()bool)
    id = 325, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 332, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 333, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 313, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 301, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 315, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 331, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 313, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 326, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()bool))
    id = 316, level = 1 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    Scope Array order:
    316,326,313,331,315,301,313,333,332,325,284,316,314,300,332,312,330,330,315,288,298,286,325,285,332,282,331,333,326,313,299,287,282,296,279,330,325,312,297,282,314,315
    Array order:
    316,326,313,331,315,301,313,333,332,325,284,316,314,300,332,312,330,330,315,288,298,286,325,285,332,282,331,333,326,313,299,287,282,296,279,330,325,312,297,282,314,315
    After exit:
    Current level: 0
    Region 0
    id = 288, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    id = 315, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 330, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 297, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()bool))
    id = 312, level = 0 is_generic = false, scope = 0
    (Constr()bool)
    id = 279, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()bool))
    id = 278, level = 0 is_generic = false, scope = 0
    278f
    id = 296, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 287, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 299, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 300, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 314, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()bool))
    id = 284, level = 0 is_generic = false, scope = 0
    (Constr()bool)
    id = 282, level = 0 is_generic = false, scope = 0
    (Constr()bool)
    id = 332, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 333, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 285, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 313, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 325, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 301, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 331, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 286, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()bool))
    id = 298, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 326, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()bool))
    id = 316, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    Region 1
    New variable:
    id = 341, level = 0 is_generic = false, scope = 0
    New variable:
    id = 342, level = 0 is_generic = false, scope = 0
    New variable:
    id = 343, level = 0 is_generic = false, scope = 0
    Unify: 278 341
    Before exit:
    Current level: 0
    Region 0
    id = 288, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    id = 315, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 330, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 297, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()bool))
    id = 312, level = 0 is_generic = false, scope = 0
    (Constr()bool)
    id = 279, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()bool))
    id = 278, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()bool))
    id = 296, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 278, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()bool))
    id = 287, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 299, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 342, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 300, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 314, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()bool))
    id = 284, level = 0 is_generic = false, scope = 0
    (Constr()bool)
    id = 282, level = 0 is_generic = false, scope = 0
    (Constr()bool)
    id = 332, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 333, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 343, level = 0 is_generic = false, scope = 0
    (Constr()bool)
    id = 285, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 313, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 325, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 301, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 331, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()int))
    id = 286, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()bool))
    id = 298, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 326, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Constr()bool))
    id = 316, level = 0 is_generic = false, scope = 0
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    Region 1
    Scope Array order:
    316,326,298,286,331,301,325,313,285,343,333,332,282,284,314,300,342,299,287,278,296,278,279,312,297,330,315,288
    Array order:
    316,326,298,286,331,301,325,313,285,343,333,332,282,284,314,300,342,299,287,278,296,278,279,312,297,330,315,288
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
  [%expect
    {|
    New variable:
    id = 344, level = 0 is_generic = false, scope = 0
    New variable:
    id = 345, level = 1 is_generic = false, scope = 0
    New variable:
    id = 346, level = 1 is_generic = false, scope = 0
    New variable:
    id = 347, level = 1 is_generic = false, scope = 0
    New variable:
    id = 348, level = 1 is_generic = false, scope = 0
    New former:
    id = 349, level = 1 is_generic = false, scope = 0
    (Arrow 347f 348f)
    Unify: 345 349
    New former:
    id = 350, level = 1 is_generic = false, scope = 0
    (Constr()int)
    Unify: 348 350
    New variable:
    id = 351, level = 1 is_generic = false, scope = 0
    New variable:
    id = 352, level = 1 is_generic = false, scope = 0
    New former:
    id = 353, level = 1 is_generic = false, scope = 0
    (Arrow 351f 352f)
    Unify: 346 353
    New former:
    id = 354, level = 1 is_generic = false, scope = 0
    (Constr()bool)
    Unify: 352 354
    Before exit:
    Current level: 1
    Region 0
    id = 344, level = 0 is_generic = false, scope = 0
    344f
    Region 1
    id = 346, level = 1 is_generic = false, scope = 0
    (Arrow 351f(Constr()bool))
    id = 347, level = 1 is_generic = false, scope = 0
    347f
    id = 351, level = 1 is_generic = false, scope = 0
    351f
    id = 346, level = 1 is_generic = false, scope = 0
    (Arrow 351f(Constr()bool))
    id = 345, level = 1 is_generic = false, scope = 0
    (Arrow 347f(Constr()int))
    id = 352, level = 1 is_generic = false, scope = 0
    (Constr()bool)
    id = 348, level = 1 is_generic = false, scope = 0
    (Constr()int)
    id = 352, level = 1 is_generic = false, scope = 0
    (Constr()bool)
    Scope Array order:
    352,348,352,345,346,351,347,346
    Array order:
    352,348,352,345,346,351,347,346
    After exit:
    Current level: 0
    Region 0
    id = 348, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 344, level = 0 is_generic = false, scope = 0
    344f
    id = 352, level = 0 is_generic = false, scope = 0
    (Constr()bool)
    Region 1
    New variable:
    id = 355, level = 0 is_generic = false, scope = 0
    New variable:
    id = 356, level = 0 is_generic = false, scope = 0
    New variable:
    id = 357, level = 0 is_generic = false, scope = 0
    Unify: 344 355
    Before exit:
    Current level: 0
    Region 0
    id = 356, level = 0 is_generic = false, scope = 0
    356f
    id = 348, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 357, level = 0 is_generic = false, scope = 0
    (Constr()int)
    id = 344, level = 0 is_generic = false, scope = 0
    (Arrow 356f(Constr()int))
    id = 344, level = 0 is_generic = false, scope = 0
    (Arrow 356f(Constr()int))
    id = 352, level = 0 is_generic = false, scope = 0
    (Constr()bool)
    Region 1
    Scope Array order:
    352,344,344,357,348,356
    Array order:
    352,344,344,357,348,356
    After exit:
    Current level: -1
    Region 0
    Region 1
    Variables: α356
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Variable: α356
          └──Type expr: Constructor: int
       └──Desc: Let rec
          └──Value bindings:
             └──Value binding:
                └──Variable: bar
                └──Abstraction:
                   └──Variables: α351
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: α347
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: α347
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Constant: 1
             └──Value binding:
                └──Variable: foo
                └──Abstraction:
                   └──Variables: α347
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: α351
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: α351
                            └──Desc: Variable: y
                         └──Expression:
                            └──Type expr: Constructor: bool
                            └──Desc: Constant: true
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Variable: α356
                └──Type expr: Constructor: int
             └──Desc: Variable
                └──Variable: foo
                └──Type expr: Variable: α356 |}]

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
    id = 358, level = 0 is_generic = false, scope = 0
    New variable:
    id = 359, level = 1 is_generic = false, scope = 0
    New variable:
    id = 360, level = 1 is_generic = false, scope = 0
    New former:
    id = 361, level = 1 is_generic = false, scope = 0
    (Arrow 360f 359f)
    New variable:
    id = 362, level = 1 is_generic = false, scope = 0
    New variable:
    id = 363, level = 1 is_generic = false, scope = 0
    New former:
    id = 364, level = 1 is_generic = false, scope = 0
    (Arrow 362f 363f)
    Unify: 361 364
    New former:
    id = 365, level = 1 is_generic = false, scope = 0
    (Constr()unit)
    Unify: 359 365
    New variable:
    id = 366, level = 1 is_generic = false, scope = 0
    New variable:
    id = 367, level = 1 is_generic = false, scope = 0
    New former:
    id = 368, level = 1 is_generic = false, scope = 0
    (Arrow 366f 367f)
    Unify: 360 368
    Unify: 367 366
    Before exit:
    Current level: 1
    Region 0
    id = 358, level = 0 is_generic = false, scope = 0
    358f
    Region 1
    id = 359, level = 1 is_generic = false, scope = 0
    (Constr()unit)
    id = 360, level = 1 is_generic = false, scope = 0
    (Arrow 367f 367f)
    id = 367, level = 1 is_generic = false, scope = 0
    367f
    id = 367, level = 1 is_generic = false, scope = 0
    367f
    id = 361, level = 1 is_generic = false, scope = 0
    (Arrow(Arrow 367f 367f)(Constr()unit))
    id = 360, level = 1 is_generic = false, scope = 0
    (Arrow 367f 367f)
    Scope Array order:
    360,361,367,367,360,359
    Array order:
    360,361,367,367,360,359
    After exit:
    Current level: 0
    Region 0
    id = 358, level = 0 is_generic = false, scope = 0
    358f
    id = 359, level = 0 is_generic = false, scope = 0
    (Constr()unit)
    Region 1
    New variable:
    id = 369, level = 0 is_generic = false, scope = 0
    Unify: 358 369
    Before exit:
    Current level: 0
    Region 0
    id = 358, level = 0 is_generic = false, scope = 0
    (Constr()unit)
    id = 358, level = 0 is_generic = false, scope = 0
    (Constr()unit)
    id = 359, level = 0 is_generic = false, scope = 0
    (Constr()unit)
    Region 1
    Scope Array order:
    359,358,358
    Array order:
    359,358,358
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
                   └──Variables: α367
                   └──Expression:
                      └──Type expr: Constructor: unit
                      └──Desc: Application
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: α367
                                  └──Type expr: Variable: α367
                               └──Type expr: Constructor: unit
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: α367
                                     └──Type expr: Variable: α367
                                  └──Desc: Variable: f
                               └──Expression:
                                  └──Type expr: Constructor: unit
                                  └──Desc: Constant: ()
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: α367
                               └──Type expr: Variable: α367
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: α367
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Variable: α367
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
  [%expect{|
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
    id = 370, level = 0 is_generic = false, scope = 0
    New variable:
    id = 371, level = 1 is_generic = false, scope = 0
    New variable:
    id = 372, level = 2 is_generic = false, scope = 0
    Solver: bind_rigid
    Solver: bind_rigid
    New variable:
    id = 373, level = 2 is_generic = false, scope = 0
    New variable:
    id = 374, level = 2 is_generic = false, scope = 0
    New former:
    id = 375, level = 2 is_generic = false, scope = 0
    (Arrow 373f 374f)
    Unify: 372 375
    New variable:
    id = 376, level = 2 is_generic = false, scope = 0
    New variable:
    id = 377, level = 2 is_generic = false, scope = 0
    New rigid variable: 2
    id = 378, level = 2 is_generic = false, scope = 0
    New former:
    id = 379, level = 2 is_generic = false, scope = 0
    (Constr(2r)t)
    New former:
    id = 380, level = 2 is_generic = false, scope = 0
    (Arrow 376f 377f)
    Unify: 374 380
    Unify: 376 379
    New variable:
    id = 381, level = 2 is_generic = false, scope = 0
    New rigid variable: 2
    id = 382, level = 2 is_generic = false, scope = 0
    New rigid variable: 3
    id = 383, level = 2 is_generic = false, scope = 0
    New former:
    id = 384, level = 2 is_generic = false, scope = 0
    (Constr(2r 3r)eq)
    New rigid variable: 2
    id = 385, level = 2 is_generic = false, scope = 0
    New rigid variable: 3
    id = 386, level = 2 is_generic = false, scope = 0
    New former:
    id = 387, level = 2 is_generic = false, scope = 0
    (Constr(2r 3r)eq)
    Unify: 381 387
    Unify: 384 373
    New variable:
    id = 388, level = 2 is_generic = false, scope = 0
    New variable:
    id = 389, level = 2 is_generic = false, scope = 0
    New former:
    id = 390, level = 2 is_generic = false, scope = 0
    (Constr(388f 389f)eq)
    Unify: 381 390
    New rigid variable: 3
    id = 391, level = 3 is_generic = false, scope = 0
    New former:
    id = 392, level = 3 is_generic = false, scope = 0
    (Constr(3r)t)
    New rigid variable: 3
    id = 393, level = 3 is_generic = false, scope = 0
    New former:
    id = 394, level = 3 is_generic = false, scope = 0
    (Constr(3r)t)
    Unify: 377 394
    New variable:
    id = 395, level = 3 is_generic = false, scope = 0
    New variable:
    id = 396, level = 3 is_generic = false, scope = 0
    Unify: 392 395
    Before exit:
    Current level: 3
    Region 0
    id = 370, level = 0 is_generic = false, scope = 0
    370f
    Region 1
    id = 371, level = 1 is_generic = false, scope = 0
    371f
    Region 2
    id = 383, level = 2 is_generic = false, scope = 0
    3r
    id = 381, level = 2 is_generic = false, scope = 0
    (Constr(2r 3r)eq)
    id = 381, level = 2 is_generic = false, scope = 0
    (Constr(2r 3r)eq)
    id = 378, level = 2 is_generic = false, scope = 0
    2r
    id = 385, level = 2 is_generic = false, scope = 0
    2r
    id = 381, level = 2 is_generic = false, scope = 0
    (Constr(2r 3r)eq)
    id = 377, level = 2 is_generic = false, scope = 0
    (Constr(3r)t)
    id = 384, level = 2 is_generic = false, scope = 0
    (Constr(2r 3r)eq)
    id = 374, level = 2 is_generic = false, scope = 0
    (Arrow(Constr(2r)t)(Constr(3r)t))
    id = 385, level = 2 is_generic = false, scope = 0
    2r
    id = 372, level = 2 is_generic = false, scope = 0
    (Arrow(Constr(2r 3r)eq)(Arrow(Constr(2r)t)(Constr(3r)t)))
    id = 376, level = 2 is_generic = false, scope = 0
    (Constr(2r)t)
    id = 384, level = 2 is_generic = false, scope = 0
    (Constr(2r 3r)eq)
    id = 382, level = 2 is_generic = false, scope = 0
    2r
    id = 386, level = 2 is_generic = false, scope = 0
    3r
    id = 386, level = 2 is_generic = false, scope = 0
    3r
    Region 3
    id = 377, level = 2 is_generic = false, scope = 0
    (Constr(3r)t)
    id = 391, level = 3 is_generic = false, scope = 3
    3r
    id = 393, level = 3 is_generic = false, scope = 0
    3r
    id = 392, level = 3 is_generic = false, scope = 0
    (Constr(3r)t)
    id = 391, level = 3 is_generic = false, scope = 3
    3r
    id = 392, level = 3 is_generic = false, scope = 0
    (Constr(3r)t)
    Scope Array order:
    391,391,392,392,393,377
    Array order:
    377,392,391,392,393,391
    Could not flexize since rigid var is unbound
    Could not flexize since rigid var is unbound
    After exit:
    Current level: 2
    Region 0
    id = 370, level = 0 is_generic = false, scope = 0
    370f
    Region 1
    id = 371, level = 1 is_generic = false, scope = 0
    371f
    Region 2
    id = 385, level = 2 is_generic = false, scope = 0
    2r
    id = 377, level = 2 is_generic = false, scope = 0
    (Constr(3r)t)
    id = 374, level = 2 is_generic = false, scope = 0
    (Arrow(Constr(2r)t)(Constr(3r)t))
    id = 384, level = 2 is_generic = false, scope = 0
    (Constr(2r 3r)eq)
    id = 382, level = 2 is_generic = false, scope = 0
    2r
    id = 383, level = 2 is_generic = false, scope = 0
    3r
    id = 381, level = 2 is_generic = false, scope = 0
    (Constr(2r 3r)eq)
    id = 393, level = 2 is_generic = false, scope = 0
    3r
    id = 378, level = 2 is_generic = false, scope = 0
    2r
    id = 372, level = 2 is_generic = false, scope = 0
    (Arrow(Constr(2r 3r)eq)(Arrow(Constr(2r)t)(Constr(3r)t)))
    id = 376, level = 2 is_generic = false, scope = 0
    (Constr(2r)t)
    id = 386, level = 2 is_generic = false, scope = 0
    3r
    Region 3
    Before exit:
    Current level: 2
    Region 0
    id = 370, level = 0 is_generic = false, scope = 0
    370f
    Region 1
    id = 371, level = 1 is_generic = false, scope = 0
    371f
    Region 2
    id = 385, level = 2 is_generic = false, scope = 0
    2r
    id = 377, level = 2 is_generic = false, scope = 0
    (Constr(3r)t)
    id = 374, level = 2 is_generic = false, scope = 0
    (Arrow(Constr(2r)t)(Constr(3r)t))
    id = 384, level = 2 is_generic = false, scope = 0
    (Constr(2r 3r)eq)
    id = 382, level = 2 is_generic = false, scope = 0
    2r
    id = 383, level = 2 is_generic = false, scope = 0
    3r
    id = 381, level = 2 is_generic = false, scope = 0
    (Constr(2r 3r)eq)
    id = 393, level = 2 is_generic = false, scope = 0
    3r
    id = 378, level = 2 is_generic = false, scope = 0
    2r
    id = 372, level = 2 is_generic = false, scope = 0
    (Arrow(Constr(2r 3r)eq)(Arrow(Constr(2r)t)(Constr(3r)t)))
    id = 376, level = 2 is_generic = false, scope = 0
    (Constr(2r)t)
    id = 386, level = 2 is_generic = false, scope = 0
    3r
    Region 3
    Scope Array order:
    386,376,372,378,393,381,383,382,384,374,377,385
    Array order:
    386,376,372,378,393,381,383,382,384,374,377,385
    New variable:
    id = 397, level = 2 is_generic = false, scope = 0
    New variable:
    id = 398, level = 2 is_generic = false, scope = 0
    After exit:
    Current level: 1
    Region 0
    id = 370, level = 0 is_generic = false, scope = 0
    370f
    Region 1
    id = 371, level = 1 is_generic = false, scope = 0
    371f
    Region 2
    Region 3
    New variable:
    id = 399, level = 1 is_generic = false, scope = 0
    New variable:
    id = 400, level = 1 is_generic = false, scope = 0
    New variable:
    id = 401, level = 1 is_generic = false, scope = 0
    New variable:
    id = 402, level = 1 is_generic = false, scope = 0
    New variable:
    id = 403, level = 1 is_generic = false, scope = 0
    New variable:
    id = 404, level = 1 is_generic = false, scope = 0
    New variable:
    id = 405, level = 1 is_generic = false, scope = 0
    Unify: 371 399
    Before exit:
    Current level: 1
    Region 0
    id = 370, level = 0 is_generic = false, scope = 0
    370f
    Region 1
    id = 404, level = 1 is_generic = false, scope = 0
    (Constr(401f)t)
    id = 401, level = 1 is_generic = false, scope = 0
    401f
    id = 405, level = 1 is_generic = false, scope = 0
    (Constr(402f)t)
    id = 371, level = 1 is_generic = false, scope = 0
    (Arrow(Constr(401f 402f)eq)(Arrow(Constr(401f)t)(Constr(402f)t)))
    id = 400, level = 1 is_generic = false, scope = 0
    (Constr(401f 402f)eq)
    id = 402, level = 1 is_generic = false, scope = 0
    402f
    id = 403, level = 1 is_generic = false, scope = 0
    (Arrow(Constr(401f)t)(Constr(402f)t))
    id = 371, level = 1 is_generic = false, scope = 0
    (Arrow(Constr(401f 402f)eq)(Arrow(Constr(401f)t)(Constr(402f)t)))
    Region 2
    Region 3
    Scope Array order:
    371,403,402,400,371,405,401,404
    Array order:
    371,403,402,400,371,405,401,404
    After exit:
    Current level: 0
    Region 0
    id = 370, level = 0 is_generic = false, scope = 0
    370f
    Region 1
    Region 2
    Region 3
    New former:
    id = 406, level = 0 is_generic = false, scope = 0
    (Constr()unit)
    Unify: 370 406
    Before exit:
    Current level: 0
    Region 0
    id = 370, level = 0 is_generic = false, scope = 0
    (Constr()unit)
    id = 370, level = 0 is_generic = false, scope = 0
    (Constr()unit)
    Region 1
    Region 2
    Region 3
    Scope Array order:
    370,370
    Array order:
    370,370
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
                   └──Type expr: Arrow
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: α401
                         └──Type expr: Variable: α402
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: α401
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: α402
                   └──Desc: Variable: coerce
                └──Abstraction:
                   └──Variables: α402,α401
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: α401
                            └──Type expr: Variable: α402
                         └──Type expr: Arrow
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: α401
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: α402
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: α397
                               └──Type expr: Variable: α398
                            └──Desc: Variable: eq
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: α397
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: α398
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: α397
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: α398
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: α397
                                           └──Type expr: Variable: α398
                                        └──Desc: Variable
                                           └──Variable: eq
                                     └──Type expr: Constructor: eq
                                        └──Type expr: Variable: α397
                                        └──Type expr: Variable: α398
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: α397
                                                 └──Type expr: Variable: α398
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Refl
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: α397
                                                          └──Type expr: Variable: α398
                                           └──Expression:
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: α398
                                              └──Desc: Variable
                                                 └──Variable: x
          └──Expression:
             └──Type expr: Constructor: unit
             └──Desc: Constant: () |}]

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