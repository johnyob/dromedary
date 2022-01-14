open! Import
open Parsetree
open Ast_types
open Types
module Constraint = Typing.Import.Constraint
module Abbreviations = Constraint.Abbreviations

let print_constraint_result ~env exp =
  let t = Infer.Expression.infer exp |> Computation.Expression.run ~env in
  let output =
    match t with
    | Ok t -> Constraint.sexp_of_t t
    | Error err -> err
  in
  output |> Sexp.to_string_hum |> print_endline


let print_infer_result ~abbrev_ctx ~env exp =
  let texp = Infer.infer ~ctx:abbrev_ctx ~env exp in
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
    ; type_params = params
    ; type_kind =
        Type_variant
          [ { constructor_name = "Nil"
            ; constructor_type_params = params
            ; constructor_arg = None
            ; constructor_type = type_
            }
          ; { constructor_name = "Cons"
            ; constructor_type_params = params
            ; constructor_arg =
                Some
                  (Ttyp_tuple
                     [ Ttyp_var "a"; Ttyp_constr ([ Ttyp_var "a" ], name) ])
            ; constructor_type = type_
            }
          ]
    }


let%expect_test "constant: int" =
  let exp = Pexp_const (Const_int 1) in
  print_infer_result ~abbrev_ctx:Abbreviations.Ctx.empty ~env:Env.empty exp;
  [%expect
    {|
    New variable:
    id = 0, level = 0, is_generic = false, flexibility = Flexible
    New former:
    id = 1, level = 0, is_generic = false
    (Constr()int)
    Unify: 0 1
    Before exit:
    Current level: 0
    Region 0
    id = 0, level = 0, is_generic = false
    (Constr()int)
    id = 0, level = 0, is_generic = false
    (Constr()int)
    Array order:
    0,0
    is young? 0 = true
    Generalizing 0
    Generalizing 0
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
  print_infer_result ~abbrev_ctx:Abbreviations.Ctx.empty ~env:Env.empty exp;
  [%expect
    {|
    New variable:
    id = 2, level = 0, is_generic = false, flexibility = Flexible
    New former:
    id = 3, level = 0, is_generic = false
    (Constr()bool)
    Unify: 2 3
    Before exit:
    Current level: 0
    Region 0
    id = 2, level = 0, is_generic = false
    (Constr()bool)
    id = 2, level = 0, is_generic = false
    (Constr()bool)
    Array order:
    2,2
    is young? 2 = true
    Generalizing 2
    Generalizing 2
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
  print_infer_result ~abbrev_ctx:Abbreviations.Ctx.empty ~env:Env.empty exp;
  [%expect
    {|
    New variable:
    id = 4, level = 0, is_generic = false, flexibility = Flexible
    New former:
    id = 5, level = 0, is_generic = false
    (Constr()unit)
    Unify: 4 5
    Before exit:
    Current level: 0
    Region 0
    id = 4, level = 0, is_generic = false
    (Constr()unit)
    id = 4, level = 0, is_generic = false
    (Constr()unit)
    Array order:
    4,4
    is young? 4 = true
    Generalizing 4
    Generalizing 4
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
  print_infer_result ~abbrev_ctx:Abbreviations.Ctx.empty ~env:Env.empty exp;
  [%expect
    {|
    New variable:
    id = 6, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 7, level = 0, is_generic = false, flexibility = Flexible
    New former:
    id = 8, level = 0, is_generic = false
    (Constr()int)
    Unify: 7 8
    New former:
    id = 9, level = 0, is_generic = false
    (Arrow(Constr()int)6)
    New variable:
    id = 10, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 11, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 12, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 13, level = 0, is_generic = false, flexibility = Flexible
    New former:
    id = 14, level = 0, is_generic = false
    (Constr()int)
    Unify: 13 14
    New former:
    id = 15, level = 0, is_generic = false
    (Arrow(Constr()int)12)
    New variable:
    id = 16, level = 0, is_generic = false, flexibility = Flexible
    New former:
    id = 17, level = 0, is_generic = false
    (Constr()int)
    Unify: 16 17
    New former:
    id = 18, level = 0, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)12))
    New former:
    id = 19, level = 0, is_generic = false
    (Constr()int)
    New former:
    id = 20, level = 0, is_generic = false
    (Constr()int)
    New former:
    id = 21, level = 0, is_generic = false
    (Constr()int)
    New former:
    id = 22, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    New former:
    id = 23, level = 0, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    Unify: 18 23
    New former:
    id = 24, level = 0, is_generic = false
    (Arrow(Constr()int)11)
    New variable:
    id = 25, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 26, level = 0, is_generic = false, flexibility = Flexible
    New former:
    id = 27, level = 0, is_generic = false
    (Constr()int)
    Unify: 26 27
    New former:
    id = 28, level = 0, is_generic = false
    (Arrow(Constr()int)25)
    New variable:
    id = 29, level = 0, is_generic = false, flexibility = Flexible
    New former:
    id = 30, level = 0, is_generic = false
    (Constr()int)
    Unify: 29 30
    New former:
    id = 31, level = 0, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)25))
    New former:
    id = 32, level = 0, is_generic = false
    (Constr()int)
    New former:
    id = 33, level = 0, is_generic = false
    (Constr()int)
    New former:
    id = 34, level = 0, is_generic = false
    (Constr()int)
    New former:
    id = 35, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    New former:
    id = 36, level = 0, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    Unify: 31 36
    New former:
    id = 37, level = 0, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)11))
    New former:
    id = 38, level = 0, is_generic = false
    (Constr()int)
    New former:
    id = 39, level = 0, is_generic = false
    (Constr()int)
    New former:
    id = 40, level = 0, is_generic = false
    (Constr()int)
    New former:
    id = 41, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    New former:
    id = 42, level = 0, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    Unify: 37 42
    New former:
    id = 43, level = 0, is_generic = false
    (Arrow(Constr()int)10)
    New variable:
    id = 44, level = 0, is_generic = false, flexibility = Flexible
    New former:
    id = 45, level = 0, is_generic = false
    (Constr()int)
    Unify: 44 45
    New former:
    id = 46, level = 0, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)10))
    New former:
    id = 47, level = 0, is_generic = false
    (Constr()int)
    New former:
    id = 48, level = 0, is_generic = false
    (Constr()int)
    New former:
    id = 49, level = 0, is_generic = false
    (Constr()int)
    New former:
    id = 50, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    New former:
    id = 51, level = 0, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    Unify: 46 51
    New former:
    id = 52, level = 0, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)6))
    New former:
    id = 53, level = 0, is_generic = false
    (Constr()int)
    New former:
    id = 54, level = 0, is_generic = false
    (Constr()int)
    New former:
    id = 55, level = 0, is_generic = false
    (Constr()bool)
    New former:
    id = 56, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()bool))
    New former:
    id = 57, level = 0, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    Unify: 52 57
    Before exit:
    Current level: 0
    Region 0
    id = 43, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    id = 29, level = 0, is_generic = false
    (Constr()int)
    id = 46, level = 0, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 7, level = 0, is_generic = false
    (Constr()int)
    id = 13, level = 0, is_generic = false
    (Constr()int)
    id = 46, level = 0, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 9, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()bool))
    id = 11, level = 0, is_generic = false
    (Constr()int)
    id = 10, level = 0, is_generic = false
    (Constr()int)
    id = 26, level = 0, is_generic = false
    (Constr()int)
    id = 52, level = 0, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    id = 37, level = 0, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 16, level = 0, is_generic = false
    (Constr()int)
    id = 24, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    id = 44, level = 0, is_generic = false
    (Constr()int)
    id = 44, level = 0, is_generic = false
    (Constr()int)
    id = 28, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    id = 10, level = 0, is_generic = false
    (Constr()int)
    id = 7, level = 0, is_generic = false
    (Constr()int)
    id = 11, level = 0, is_generic = false
    (Constr()int)
    id = 12, level = 0, is_generic = false
    (Constr()int)
    id = 31, level = 0, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 9, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()bool))
    id = 15, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    id = 6, level = 0, is_generic = false
    (Constr()bool)
    id = 6, level = 0, is_generic = false
    (Constr()bool)
    id = 10, level = 0, is_generic = false
    (Constr()int)
    id = 52, level = 0, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    id = 25, level = 0, is_generic = false
    (Constr()int)
    id = 43, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    id = 18, level = 0, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    Array order:
    18,43,25,52,10,6,6,15,9,31,12,11,7,10,28,44,44,24,16,37,52,26,10,11,9,46,13,7,46,29,43
    is young? 18 = true
    is young? 15 = true
    is young? 12 = true
    is young? 13 = true
    is young? 16 = true
    is young? 43 = true
    is young? 10 = true
    is young? 11 = true
    is young? 25 = true
    is young? 52 = true
    is young? 9 = true
    is young? 6 = true
    is young? 7 = true
    is young? 31 = true
    is young? 28 = true
    is young? 26 = true
    is young? 29 = true
    is young? 44 = true
    is young? 24 = true
    is young? 37 = true
    is young? 46 = true
    Generalizing 43
    Generalizing 29
    Generalizing 46
    Generalizing 7
    Generalizing 13
    Generalizing 46
    Generalizing 9
    Generalizing 11
    Generalizing 10
    Generalizing 26
    Generalizing 52
    Generalizing 37
    Generalizing 16
    Generalizing 24
    Generalizing 44
    Generalizing 44
    Generalizing 28
    Generalizing 10
    Generalizing 7
    Generalizing 11
    Generalizing 12
    Generalizing 31
    Generalizing 9
    Generalizing 15
    Generalizing 6
    Generalizing 6
    Generalizing 10
    Generalizing 52
    Generalizing 25
    Generalizing 43
    Generalizing 18
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
  print_infer_result ~abbrev_ctx:Abbreviations.Ctx.empty ~env:Env.empty exp;
  [%expect
    {|
    New variable:
    id = 58, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 59, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 60, level = 0, is_generic = false, flexibility = Flexible
    Instantiating: 59
    Copying 59
    Instantiated result:
    59
    Unify: 60 59
    New former:
    id = 61, level = 0, is_generic = false
    (Arrow 60 60)
    Unify: 58 61
    Before exit:
    Current level: 0
    Region 0
    id = 60, level = 0, is_generic = false, flexibility = Flexible
    60
    id = 58, level = 0, is_generic = false
    (Arrow 60 60)
    id = 60, level = 0, is_generic = false, flexibility = Flexible
    60
    id = 58, level = 0, is_generic = false
    (Arrow 60 60)
    Array order:
    58,60,58,60
    is young? 58 = true
    is young? 60 = true
    Generalizing 60
    Generalizing 58
    Generalizing 60
    Generalizing 58
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
  print_infer_result ~abbrev_ctx:Abbreviations.Ctx.empty ~env:Env.empty exp;
  [%expect
    {|
    New variable:
    id = 62, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 63, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 64, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 65, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 66, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 67, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 68, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 69, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 70, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 71, level = 0, is_generic = false, flexibility = Flexible
    Instantiating: 67
    Copying 67
    Instantiated result:
    67
    Unify: 71 67
    Instantiating: 65
    Copying 65
    Instantiated result:
    65
    Unify: 70 65
    New former:
    id = 72, level = 0, is_generic = false
    (Tuple(70 71))
    Unify: 69 72
    New former:
    id = 73, level = 0, is_generic = false
    (Arrow(Tuple(70 71))68)
    Instantiating: 63
    Copying 63
    Instantiated result:
    63
    Unify: 73 63
    New former:
    id = 74, level = 0, is_generic = false
    (Arrow 71 68)
    Unify: 66 74
    New former:
    id = 75, level = 0, is_generic = false
    (Arrow 70(Arrow 71 68))
    Unify: 64 75
    New former:
    id = 76, level = 0, is_generic = false
    (Arrow(Arrow(Tuple(70 71))68)(Arrow 70(Arrow 71 68)))
    Unify: 62 76
    Before exit:
    Current level: 0
    Region 0
    id = 71, level = 0, is_generic = false, flexibility = Flexible
    71
    id = 62, level = 0, is_generic = false
    (Arrow(Arrow(Tuple(70 71))68)(Arrow 70(Arrow 71 68)))
    id = 64, level = 0, is_generic = false
    (Arrow 70(Arrow 71 68))
    id = 69, level = 0, is_generic = false
    (Tuple(70 71))
    id = 64, level = 0, is_generic = false
    (Arrow 70(Arrow 71 68))
    id = 62, level = 0, is_generic = false
    (Arrow(Arrow(Tuple(70 71))68)(Arrow 70(Arrow 71 68)))
    id = 69, level = 0, is_generic = false
    (Tuple(70 71))
    id = 66, level = 0, is_generic = false
    (Arrow 71 68)
    id = 73, level = 0, is_generic = false
    (Arrow(Tuple(70 71))68)
    id = 66, level = 0, is_generic = false
    (Arrow 71 68)
    id = 70, level = 0, is_generic = false, flexibility = Flexible
    70
    id = 71, level = 0, is_generic = false, flexibility = Flexible
    71
    id = 73, level = 0, is_generic = false
    (Arrow(Tuple(70 71))68)
    id = 70, level = 0, is_generic = false, flexibility = Flexible
    70
    id = 68, level = 0, is_generic = false, flexibility = Flexible
    68
    Array order:
    68,70,73,71,70,66,73,66,69,62,64,69,64,62,71
    is young? 68 = true
    is young? 70 = true
    is young? 73 = true
    is young? 69 = true
    is young? 71 = true
    is young? 66 = true
    is young? 62 = true
    is young? 64 = true
    Generalizing 71
    Generalizing 62
    Generalizing 64
    Generalizing 69
    Generalizing 64
    Generalizing 62
    Generalizing 69
    Generalizing 66
    Generalizing 73
    Generalizing 66
    Generalizing 70
    Generalizing 71
    Generalizing 73
    Generalizing 70
    Generalizing 68
    After exit:
    Current level: -1
    Region 0
    Variables: α68,α70,α71
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Arrow
             └──Type expr: Tuple
                └──Type expr: Variable: α70
                └──Type expr: Variable: α71
             └──Type expr: Variable: α68
          └──Type expr: Arrow
             └──Type expr: Variable: α70
             └──Type expr: Arrow
                └──Type expr: Variable: α71
                └──Type expr: Variable: α68
       └──Desc: Function
          └──Pattern:
             └──Type expr: Arrow
                └──Type expr: Tuple
                   └──Type expr: Variable: α70
                   └──Type expr: Variable: α71
                └──Type expr: Variable: α68
             └──Desc: Variable: f
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Variable: α70
                └──Type expr: Arrow
                   └──Type expr: Variable: α71
                   └──Type expr: Variable: α68
             └──Desc: Function
                └──Pattern:
                   └──Type expr: Variable: α70
                   └──Desc: Variable: x
                └──Expression:
                   └──Type expr: Arrow
                      └──Type expr: Variable: α71
                      └──Type expr: Variable: α68
                   └──Desc: Function
                      └──Pattern:
                         └──Type expr: Variable: α71
                         └──Desc: Variable: y
                      └──Expression:
                         └──Type expr: Variable: α68
                         └──Desc: Application
                            └──Expression:
                               └──Type expr: Arrow
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: α70
                                     └──Type expr: Variable: α71
                                  └──Type expr: Variable: α68
                               └──Desc: Variable
                                  └──Variable: f
                            └──Expression:
                               └──Type expr: Tuple
                                  └──Type expr: Variable: α70
                                  └──Type expr: Variable: α71
                               └──Desc: Tuple
                                  └──Expression:
                                     └──Type expr: Variable: α70
                                     └──Desc: Variable
                                        └──Variable: x
                                  └──Expression:
                                     └──Type expr: Variable: α71
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
  print_infer_result ~abbrev_ctx:Abbreviations.Ctx.empty ~env:Env.empty exp;
  [%expect
    {|
    New variable:
    id = 77, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 78, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 79, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 80, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 81, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 82, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 83, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 84, level = 0, is_generic = false, flexibility = Flexible
    Instantiating: 82
    Copying 82
    Instantiated result:
    82
    Unify: 84 82
    New former:
    id = 85, level = 0, is_generic = false
    (Arrow 84 81)
    New variable:
    id = 86, level = 0, is_generic = false, flexibility = Flexible
    Instantiating: 83
    Copying 83
    Instantiated result:
    83
    Unify: 86 83
    New former:
    id = 87, level = 0, is_generic = false
    (Arrow 86(Arrow 84 81))
    Instantiating: 78
    Copying 78
    Instantiated result:
    78
    Unify: 87 78
    New former:
    id = 88, level = 0, is_generic = false
    (Tuple(86 84))
    Unify: 80 88
    New former:
    id = 89, level = 0, is_generic = false
    (Arrow(Tuple(86 84))81)
    Unify: 79 89
    New former:
    id = 90, level = 0, is_generic = false
    (Arrow(Arrow 86(Arrow 84 81))(Arrow(Tuple(86 84))81))
    Unify: 77 90
    Before exit:
    Current level: 0
    Region 0
    id = 86, level = 0, is_generic = false, flexibility = Flexible
    86
    id = 80, level = 0, is_generic = false
    (Tuple(86 84))
    id = 86, level = 0, is_generic = false, flexibility = Flexible
    86
    id = 84, level = 0, is_generic = false, flexibility = Flexible
    84
    id = 77, level = 0, is_generic = false
    (Arrow(Arrow 86(Arrow 84 81))(Arrow(Tuple(86 84))81))
    id = 87, level = 0, is_generic = false
    (Arrow 86(Arrow 84 81))
    id = 79, level = 0, is_generic = false
    (Arrow(Tuple(86 84))81)
    id = 81, level = 0, is_generic = false, flexibility = Flexible
    81
    id = 80, level = 0, is_generic = false
    (Tuple(86 84))
    id = 77, level = 0, is_generic = false
    (Arrow(Arrow 86(Arrow 84 81))(Arrow(Tuple(86 84))81))
    id = 87, level = 0, is_generic = false
    (Arrow 86(Arrow 84 81))
    id = 85, level = 0, is_generic = false
    (Arrow 84 81)
    id = 79, level = 0, is_generic = false
    (Arrow(Tuple(86 84))81)
    Array order:
    79,85,87,77,80,81,79,87,77,84,86,80,86
    is young? 79 = true
    is young? 81 = true
    is young? 80 = true
    is young? 84 = true
    is young? 86 = true
    is young? 85 = true
    is young? 87 = true
    is young? 77 = true
    Generalizing 86
    Generalizing 80
    Generalizing 86
    Generalizing 84
    Generalizing 77
    Generalizing 87
    Generalizing 79
    Generalizing 81
    Generalizing 80
    Generalizing 77
    Generalizing 87
    Generalizing 85
    Generalizing 79
    After exit:
    Current level: -1
    Region 0
    Variables: α81,α84,α86
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Arrow
             └──Type expr: Variable: α86
             └──Type expr: Arrow
                └──Type expr: Variable: α84
                └──Type expr: Variable: α81
          └──Type expr: Arrow
             └──Type expr: Tuple
                └──Type expr: Variable: α86
                └──Type expr: Variable: α84
             └──Type expr: Variable: α81
       └──Desc: Function
          └──Pattern:
             └──Type expr: Arrow
                └──Type expr: Variable: α86
                └──Type expr: Arrow
                   └──Type expr: Variable: α84
                   └──Type expr: Variable: α81
             └──Desc: Variable: f
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Tuple
                   └──Type expr: Variable: α86
                   └──Type expr: Variable: α84
                └──Type expr: Variable: α81
             └──Desc: Function
                └──Pattern:
                   └──Type expr: Tuple
                      └──Type expr: Variable: α86
                      └──Type expr: Variable: α84
                   └──Desc: Tuple
                      └──Pattern:
                         └──Type expr: Variable: α86
                         └──Desc: Variable: x
                      └──Pattern:
                         └──Type expr: Variable: α84
                         └──Desc: Variable: y
                └──Expression:
                   └──Type expr: Variable: α81
                   └──Desc: Application
                      └──Expression:
                         └──Type expr: Arrow
                            └──Type expr: Variable: α84
                            └──Type expr: Variable: α81
                         └──Desc: Application
                            └──Expression:
                               └──Type expr: Arrow
                                  └──Type expr: Variable: α86
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: α84
                                     └──Type expr: Variable: α81
                               └──Desc: Variable
                                  └──Variable: f
                            └──Expression:
                               └──Type expr: Variable: α86
                               └──Desc: Variable
                                  └──Variable: x
                      └──Expression:
                         └──Type expr: Variable: α84
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
  print_infer_result ~abbrev_ctx:Abbreviations.Ctx.empty ~env:Env.empty exp;
  [%expect
    {|
    New variable:
    id = 91, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 92, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 93, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 94, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 95, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 96, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 97, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 98, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 99, level = 0, is_generic = false, flexibility = Flexible
    Instantiating: 96
    Copying 96
    Instantiated result:
    96
    Unify: 99 96
    New former:
    id = 100, level = 0, is_generic = false
    (Arrow 99 98)
    Instantiating: 94
    Copying 94
    Instantiated result:
    94
    Unify: 100 94
    New former:
    id = 101, level = 0, is_generic = false
    (Arrow 98 97)
    Instantiating: 92
    Copying 92
    Instantiated result:
    92
    Unify: 101 92
    New former:
    id = 102, level = 0, is_generic = false
    (Arrow 99 97)
    Unify: 95 102
    New former:
    id = 103, level = 0, is_generic = false
    (Arrow(Arrow 99 98)(Arrow 99 97))
    Unify: 93 103
    New former:
    id = 104, level = 0, is_generic = false
    (Arrow(Arrow 98 97)(Arrow(Arrow 99 98)(Arrow 99 97)))
    Unify: 91 104
    Before exit:
    Current level: 0
    Region 0
    id = 93, level = 0, is_generic = false
    (Arrow(Arrow 99 98)(Arrow 99 97))
    id = 99, level = 0, is_generic = false, flexibility = Flexible
    99
    id = 100, level = 0, is_generic = false
    (Arrow 99 98)
    id = 99, level = 0, is_generic = false, flexibility = Flexible
    99
    id = 95, level = 0, is_generic = false
    (Arrow 99 97)
    id = 93, level = 0, is_generic = false
    (Arrow(Arrow 99 98)(Arrow 99 97))
    id = 97, level = 0, is_generic = false, flexibility = Flexible
    97
    id = 101, level = 0, is_generic = false
    (Arrow 98 97)
    id = 91, level = 0, is_generic = false
    (Arrow(Arrow 98 97)(Arrow(Arrow 99 98)(Arrow 99 97)))
    id = 98, level = 0, is_generic = false, flexibility = Flexible
    98
    id = 91, level = 0, is_generic = false
    (Arrow(Arrow 98 97)(Arrow(Arrow 99 98)(Arrow 99 97)))
    id = 101, level = 0, is_generic = false
    (Arrow 98 97)
    id = 100, level = 0, is_generic = false
    (Arrow 99 98)
    id = 95, level = 0, is_generic = false
    (Arrow 99 97)
    Array order:
    95,100,101,91,98,91,101,97,93,95,99,100,99,93
    is young? 95 = true
    is young? 97 = true
    is young? 99 = true
    is young? 100 = true
    is young? 98 = true
    is young? 101 = true
    is young? 91 = true
    is young? 93 = true
    Generalizing 93
    Generalizing 99
    Generalizing 100
    Generalizing 99
    Generalizing 95
    Generalizing 93
    Generalizing 97
    Generalizing 101
    Generalizing 91
    Generalizing 98
    Generalizing 91
    Generalizing 101
    Generalizing 100
    Generalizing 95
    After exit:
    Current level: -1
    Region 0
    Variables: α98,α97,α99
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Arrow
             └──Type expr: Variable: α98
             └──Type expr: Variable: α97
          └──Type expr: Arrow
             └──Type expr: Arrow
                └──Type expr: Variable: α99
                └──Type expr: Variable: α98
             └──Type expr: Arrow
                └──Type expr: Variable: α99
                └──Type expr: Variable: α97
       └──Desc: Function
          └──Pattern:
             └──Type expr: Arrow
                └──Type expr: Variable: α98
                └──Type expr: Variable: α97
             └──Desc: Variable: f
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Arrow
                   └──Type expr: Variable: α99
                   └──Type expr: Variable: α98
                └──Type expr: Arrow
                   └──Type expr: Variable: α99
                   └──Type expr: Variable: α97
             └──Desc: Function
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: α99
                      └──Type expr: Variable: α98
                   └──Desc: Variable: g
                └──Expression:
                   └──Type expr: Arrow
                      └──Type expr: Variable: α99
                      └──Type expr: Variable: α97
                   └──Desc: Function
                      └──Pattern:
                         └──Type expr: Variable: α99
                         └──Desc: Variable: x
                      └──Expression:
                         └──Type expr: Variable: α97
                         └──Desc: Application
                            └──Expression:
                               └──Type expr: Arrow
                                  └──Type expr: Variable: α98
                                  └──Type expr: Variable: α97
                               └──Desc: Variable
                                  └──Variable: f
                            └──Expression:
                               └──Type expr: Variable: α98
                               └──Desc: Application
                                  └──Expression:
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: α99
                                        └──Type expr: Variable: α98
                                     └──Desc: Variable
                                        └──Variable: g
                                  └──Expression:
                                     └──Type expr: Variable: α99
                                     └──Desc: Variable
                                        └──Variable: x |}]

let%expect_test "function - fst" =
  let exp =
    (* fun (x, y) -> x *)
    Pexp_fun (Ppat_tuple [ Ppat_var "x"; Ppat_var "y" ], Pexp_var "x")
  in
  print_infer_result ~abbrev_ctx:Abbreviations.Ctx.empty ~env:Env.empty exp;
  [%expect
    {|
    New variable:
    id = 105, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 106, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 107, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 108, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 109, level = 0, is_generic = false, flexibility = Flexible
    Instantiating: 109
    Copying 109
    Instantiated result:
    109
    Unify: 107 109
    New former:
    id = 110, level = 0, is_generic = false
    (Tuple(107 108))
    Unify: 106 110
    New former:
    id = 111, level = 0, is_generic = false
    (Arrow(Tuple(107 108))107)
    Unify: 105 111
    Before exit:
    Current level: 0
    Region 0
    id = 105, level = 0, is_generic = false
    (Arrow(Tuple(107 108))107)
    id = 107, level = 0, is_generic = false, flexibility = Flexible
    107
    id = 105, level = 0, is_generic = false
    (Arrow(Tuple(107 108))107)
    id = 106, level = 0, is_generic = false
    (Tuple(107 108))
    id = 107, level = 0, is_generic = false, flexibility = Flexible
    107
    id = 108, level = 0, is_generic = false, flexibility = Flexible
    108
    id = 106, level = 0, is_generic = false
    (Tuple(107 108))
    Array order:
    106,108,107,106,105,107,105
    is young? 106 = true
    is young? 108 = true
    is young? 107 = true
    is young? 105 = true
    Generalizing 105
    Generalizing 107
    Generalizing 105
    Generalizing 106
    Generalizing 107
    Generalizing 108
    Generalizing 106
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
  print_infer_result ~abbrev_ctx:Abbreviations.Ctx.empty ~env:Env.empty exp;
  [%expect
    {|
    New variable:
    id = 112, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 113, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 114, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 115, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 116, level = 0, is_generic = false, flexibility = Flexible
    Instantiating: 115
    Copying 115
    Instantiated result:
    115
    Unify: 114 115
    New former:
    id = 117, level = 0, is_generic = false
    (Tuple(116 114))
    Unify: 113 117
    New former:
    id = 118, level = 0, is_generic = false
    (Arrow(Tuple(116 114))114)
    Unify: 112 118
    Before exit:
    Current level: 0
    Region 0
    id = 113, level = 0, is_generic = false
    (Tuple(116 114))
    id = 114, level = 0, is_generic = false, flexibility = Flexible
    114
    id = 114, level = 0, is_generic = false, flexibility = Flexible
    114
    id = 112, level = 0, is_generic = false
    (Arrow(Tuple(116 114))114)
    id = 112, level = 0, is_generic = false
    (Arrow(Tuple(116 114))114)
    id = 116, level = 0, is_generic = false, flexibility = Flexible
    116
    id = 113, level = 0, is_generic = false
    (Tuple(116 114))
    Array order:
    113,116,112,112,114,114,113
    is young? 113 = true
    is young? 114 = true
    is young? 116 = true
    is young? 112 = true
    Generalizing 113
    Generalizing 114
    Generalizing 114
    Generalizing 112
    Generalizing 112
    Generalizing 116
    Generalizing 113
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
      ( Ppat_construct ("Cons", Some (Ppat_tuple [ Ppat_var "x"; Ppat_any ]))
      , Pexp_var "x" )
  in
  print_infer_result ~abbrev_ctx:Abbreviations.Ctx.empty ~env exp;
  [%expect
    {|
    New variable:
    id = 119, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 120, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 121, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 122, level = 0, is_generic = false, flexibility = Flexible
    New former:
    id = 123, level = 0, is_generic = false
    (Constr(122)list)
    New former:
    id = 124, level = 0, is_generic = false
    (Tuple(122(Constr(122)list)))
    New former:
    id = 125, level = 0, is_generic = false
    (Constr(122)list)
    New variable:
    id = 126, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 127, level = 0, is_generic = false, flexibility = Flexible
    Instantiating: 127
    Copying 127
    Instantiated result:
    127
    Unify: 121 127
    New former:
    id = 128, level = 0, is_generic = false
    (Tuple(121 126))
    Unify: 124 128
    Unify: 120 125
    New former:
    id = 129, level = 0, is_generic = false
    (Arrow(Constr(122)list)122)
    Unify: 119 129
    Before exit:
    Current level: 0
    Region 0
    id = 120, level = 0, is_generic = false
    (Constr(122)list)
    id = 119, level = 0, is_generic = false
    (Arrow(Constr(122)list)122)
    id = 122, level = 0, is_generic = false, flexibility = Flexible
    122
    id = 123, level = 0, is_generic = false
    (Constr(122)list)
    id = 123, level = 0, is_generic = false
    (Constr(122)list)
    id = 120, level = 0, is_generic = false
    (Constr(122)list)
    id = 122, level = 0, is_generic = false, flexibility = Flexible
    122
    id = 124, level = 0, is_generic = false
    (Tuple(122(Constr(122)list)))
    id = 124, level = 0, is_generic = false
    (Tuple(122(Constr(122)list)))
    id = 119, level = 0, is_generic = false
    (Arrow(Constr(122)list)122)
    id = 122, level = 0, is_generic = false, flexibility = Flexible
    122
    Array order:
    122,119,124,124,122,120,123,123,122,119,120
    is young? 122 = true
    is young? 119 = true
    is young? 120 = true
    is young? 124 = true
    is young? 123 = true
    Generalizing 120
    Generalizing 119
    Generalizing 122
    Generalizing 123
    Generalizing 123
    Generalizing 120
    Generalizing 122
    Generalizing 124
    Generalizing 124
    Generalizing 119
    Generalizing 122
    After exit:
    Current level: -1
    Region 0
    Variables: α122
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Constructor: list
             └──Type expr: Variable: α122
          └──Type expr: Variable: α122
       └──Desc: Function
          └──Pattern:
             └──Type expr: Constructor: list
                └──Type expr: Variable: α122
             └──Desc: Construct
                └──Constructor description:
                   └──Name: Cons
                   └──Constructor argument type:
                      └──Type expr: Tuple
                         └──Type expr: Variable: α122
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: α122
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: α122
                └──Pattern:
                   └──Type expr: Tuple
                      └──Type expr: Variable: α122
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: α122
                   └──Desc: Tuple
                      └──Pattern:
                         └──Type expr: Variable: α122
                         └──Desc: Variable: x
                      └──Pattern:
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: α122
                         └──Desc: Any
          └──Expression:
             └──Type expr: Variable: α122
             └──Desc: Variable
                └──Variable: x |}]

let%expect_test "annotation - identity" =
  let exp =
    (* exists 'a -> fun (x : 'a) -> x *)
    Pexp_exists
      ( [ "a" ]
      , Pexp_fun (Ppat_constraint (Ppat_var "x", Ptyp_var "a"), Pexp_var "x") )
  in
  print_infer_result ~abbrev_ctx:Abbreviations.Ctx.empty ~env:Env.empty exp;
  [%expect
    {|
    New variable:
    id = 130, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 131, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 132, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 133, level = 0, is_generic = false, flexibility = Flexible
    Instantiating: 131
    Copying 131
    Instantiated result:
    131
    Unify: 133 131
    Unify: 132 133
    New former:
    id = 134, level = 0, is_generic = false
    (Arrow 132 132)
    Unify: 130 134
    Before exit:
    Current level: 0
    Region 0
    id = 130, level = 0, is_generic = false
    (Arrow 132 132)
    id = 130, level = 0, is_generic = false
    (Arrow 132 132)
    id = 132, level = 0, is_generic = false, flexibility = Flexible
    132
    Array order:
    132,130,130
    is young? 132 = true
    is young? 130 = true
    Generalizing 130
    Generalizing 130
    Generalizing 132
    After exit:
    Current level: -1
    Region 0
    Variables: α132
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Variable: α132
          └──Type expr: Variable: α132
       └──Desc: Function
          └──Pattern:
             └──Type expr: Variable: α132
             └──Desc: Variable: x
          └──Expression:
             └──Type expr: Variable: α132
             └──Desc: Variable
                └──Variable: x |}]

let%expect_test "annotation - identity" =
  let exp =
    (* forall 'a -> fun (x : 'a) -> x *)
    Pexp_forall
      ( [ "a" ]
      , Pexp_fun (Ppat_constraint (Ppat_var "x", Ptyp_var "a"), Pexp_var "x") )
  in
  print_infer_result ~abbrev_ctx:Abbreviations.Ctx.empty ~env:Env.empty exp;
  [%expect
    {|
    New variable:
    id = 135, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 136, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 137, level = 1, is_generic = false, flexibility = Rigid
    New variable:
    id = 138, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 139, level = 1, is_generic = false, flexibility = Flexible
    Instantiating: 137
    Copying 137
    Instantiated result:
    137
    Unify: 139 137
    Unify: 138 139
    New former:
    id = 140, level = 1, is_generic = false
    (Arrow 138 138)
    Unify: 136 140
    Before exit:
    Current level: 1
    Region 0
    id = 135, level = 0, is_generic = false, flexibility = Flexible
    135
    Region 1
    id = 136, level = 1, is_generic = false
    (Arrow 138 138)
    id = 138, level = 1, is_generic = false, flexibility = Rigid
    138
    id = 136, level = 1, is_generic = false
    (Arrow 138 138)
    Array order:
    136,138,136
    is young? 136 = true
    is young? 138 = true
    Generalizing 136
    Generalizing 138
    Generalizing 136
    After exit:
    Current level: 0
    Region 0
    id = 135, level = 0, is_generic = false, flexibility = Flexible
    135
    Region 1
    Instantiating: 136
    Copying 136
    136 is generic
    New variable:
    id = 141, level = 0, is_generic = false, flexibility = Flexible
    Productive_view_map copy
    Copying 138
    138 is generic
    New variable:
    id = 142, level = 0, is_generic = false, flexibility = Flexible
    Copying 138
    138 is generic
    Instantiated result:
    (Arrow 142 142)
    Unify: 135 141
    Before exit:
    Current level: 0
    Region 0
    id = 135, level = 0, is_generic = false
    (Arrow 142 142)
    id = 135, level = 0, is_generic = false
    (Arrow 142 142)
    id = 142, level = 0, is_generic = false, flexibility = Flexible
    142
    Region 1
    Array order:
    142,135,135
    is young? 142 = true
    is young? 135 = true
    Generalizing 135
    Generalizing 135
    Generalizing 142
    After exit:
    Current level: -1
    Region 0
    Region 1
    Variables: α142
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Variable: α142
          └──Type expr: Variable: α142
       └──Desc: Function
          └──Pattern:
             └──Type expr: Variable: α138
             └──Desc: Variable: x
          └──Expression:
             └──Type expr: Variable: α138
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
  print_infer_result ~abbrev_ctx:Abbreviations.Ctx.empty ~env:Env.empty exp;
  [%expect
    {|
    New variable:
    id = 143, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 144, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 145, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 146, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 147, level = 0, is_generic = false, flexibility = Flexible
    New former:
    id = 148, level = 0, is_generic = false
    (Constr()int)
    Unify: 147 148
    New former:
    id = 149, level = 0, is_generic = false
    (Arrow(Constr()int)146)
    New variable:
    id = 150, level = 0, is_generic = false, flexibility = Flexible
    Instantiating: 144
    Copying 144
    Instantiated result:
    144
    Unify: 150 144
    New former:
    id = 151, level = 0, is_generic = false
    (Arrow 150(Arrow(Constr()int)146))
    New former:
    id = 152, level = 0, is_generic = false
    (Constr()int)
    New former:
    id = 153, level = 0, is_generic = false
    (Constr()int)
    New former:
    id = 154, level = 0, is_generic = false
    (Constr()int)
    New former:
    id = 155, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    New former:
    id = 156, level = 0, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    Unify: 151 156
    Unify: 145 150
    New former:
    id = 157, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    Unify: 143 157
    Before exit:
    Current level: 0
    Region 0
    id = 149, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    id = 147, level = 0, is_generic = false
    (Constr()int)
    id = 146, level = 0, is_generic = false
    (Constr()int)
    id = 145, level = 0, is_generic = false
    (Constr()int)
    id = 145, level = 0, is_generic = false
    (Constr()int)
    id = 145, level = 0, is_generic = false
    (Constr()int)
    id = 147, level = 0, is_generic = false
    (Constr()int)
    id = 151, level = 0, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 143, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    id = 149, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    id = 146, level = 0, is_generic = false
    (Constr()int)
    id = 143, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    id = 151, level = 0, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    Array order:
    151,143,146,149,143,151,147,145,145,145,146,147,149
    is young? 151 = true
    is young? 149 = true
    is young? 146 = true
    is young? 147 = true
    is young? 145 = true
    is young? 143 = true
    Generalizing 149
    Generalizing 147
    Generalizing 146
    Generalizing 145
    Generalizing 145
    Generalizing 145
    Generalizing 147
    Generalizing 151
    Generalizing 143
    Generalizing 149
    Generalizing 146
    Generalizing 143
    Generalizing 151
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
  print_infer_result ~abbrev_ctx:Abbreviations.Ctx.empty ~env:Env.empty exp;
  [%expect
    {|
    New variable:
    id = 158, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 159, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 160, level = 1, is_generic = false, flexibility = Rigid
    New variable:
    id = 161, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 162, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 163, level = 1, is_generic = false, flexibility = Flexible
    New former:
    id = 164, level = 1, is_generic = false
    (Constr()int)
    Unify: 163 164
    New former:
    id = 165, level = 1, is_generic = false
    (Arrow(Constr()int)162)
    New variable:
    id = 166, level = 1, is_generic = false, flexibility = Flexible
    Instantiating: 160
    Copying 160
    Instantiated result:
    160
    Unify: 166 160
    New former:
    id = 167, level = 1, is_generic = false
    (Arrow 166(Arrow(Constr()int)162))
    New former:
    id = 168, level = 1, is_generic = false
    (Constr()int)
    New former:
    id = 169, level = 1, is_generic = false
    (Constr()int)
    New former:
    id = 170, level = 1, is_generic = false
    (Constr()int)
    New former:
    id = 171, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    New former:
    id = 172, level = 1, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    Unify: 167 172
    ("Cannot unify types"
     (type_expr1
      (Ttyp_arrow (Ttyp_var "\206\177166")
       (Ttyp_arrow (Ttyp_constr (() int)) (Ttyp_var "\206\177162"))))
     (type_expr2
      (Ttyp_arrow (Ttyp_constr (() int))
       (Ttyp_arrow (Ttyp_constr (() int)) (Ttyp_constr (() int)))))) |}]

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
  print_infer_result ~abbrev_ctx:Abbreviations.Ctx.empty ~env:Env.empty exp;
  [%expect
    {|
    New variable:
    id = 173, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 174, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 175, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 176, level = 1, is_generic = false, flexibility = Flexible
    Instantiating: 175
    Copying 175
    Instantiated result:
    175
    Unify: 176 175
    New former:
    id = 177, level = 1, is_generic = false
    (Arrow 176 176)
    Unify: 174 177
    Before exit:
    Current level: 1
    Region 0
    id = 173, level = 0, is_generic = false, flexibility = Flexible
    173
    Region 1
    id = 174, level = 1, is_generic = false
    (Arrow 176 176)
    id = 176, level = 1, is_generic = false, flexibility = Flexible
    176
    id = 176, level = 1, is_generic = false, flexibility = Flexible
    176
    id = 174, level = 1, is_generic = false
    (Arrow 176 176)
    Array order:
    174,176,176,174
    is young? 174 = true
    is young? 176 = true
    Generalizing 174
    Generalizing 176
    Generalizing 176
    Generalizing 174
    After exit:
    Current level: 0
    Region 0
    id = 173, level = 0, is_generic = false, flexibility = Flexible
    173
    Region 1
    New variable:
    id = 178, level = 0, is_generic = false, flexibility = Flexible
    New former:
    id = 179, level = 0, is_generic = false
    (Constr()unit)
    Unify: 178 179
    New former:
    id = 180, level = 0, is_generic = false
    (Arrow(Constr()unit)173)
    New variable:
    id = 181, level = 0, is_generic = false, flexibility = Flexible
    Instantiating: 174
    Copying 174
    174 is generic
    New variable:
    id = 182, level = 0, is_generic = false, flexibility = Flexible
    Productive_view_map copy
    Copying 176
    176 is generic
    New variable:
    id = 183, level = 0, is_generic = false, flexibility = Flexible
    Copying 176
    176 is generic
    Instantiated result:
    (Arrow 183 183)
    Unify: 181 182
    New former:
    id = 184, level = 0, is_generic = false
    (Arrow(Arrow 183 183)(Arrow(Constr()unit)173))
    Instantiating: 174
    Copying 174
    174 is generic
    New variable:
    id = 185, level = 0, is_generic = false, flexibility = Flexible
    Productive_view_map copy
    Copying 176
    176 is generic
    New variable:
    id = 186, level = 0, is_generic = false, flexibility = Flexible
    Copying 176
    176 is generic
    Instantiated result:
    (Arrow 186 186)
    Unify: 184 185
    Before exit:
    Current level: 0
    Region 0
    id = 173, level = 0, is_generic = false
    (Constr()unit)
    id = 184, level = 0, is_generic = false
    (Arrow(Arrow(Constr()unit)(Constr()unit))(Arrow(Constr()unit)(Constr()unit)))
    id = 180, level = 0, is_generic = false
    (Arrow(Constr()unit)(Constr()unit))
    id = 173, level = 0, is_generic = false
    (Constr()unit)
    id = 184, level = 0, is_generic = false
    (Arrow(Arrow(Constr()unit)(Constr()unit))(Arrow(Constr()unit)(Constr()unit)))
    id = 180, level = 0, is_generic = false
    (Arrow(Constr()unit)(Constr()unit))
    id = 173, level = 0, is_generic = false
    (Constr()unit)
    id = 180, level = 0, is_generic = false
    (Arrow(Constr()unit)(Constr()unit))
    Region 1
    Array order:
    180,173,180,184,173,180,184,173
    is young? 180 = true
    is young? 173 = true
    is young? 184 = true
    Generalizing 173
    Generalizing 184
    Generalizing 180
    Generalizing 173
    Generalizing 184
    Generalizing 180
    Generalizing 173
    Generalizing 180
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
                                      (Ppat_tuple
                                         [ Ppat_var "x"; Ppat_var "xs" ]) )
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
  print_infer_result ~abbrev_ctx:Abbreviations.Ctx.empty ~env exp;
  [%expect
    {|
    New variable:
    id = 187, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 188, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 189, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 190, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 191, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 192, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 193, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 194, level = 1, is_generic = false, flexibility = Flexible
    New former:
    id = 195, level = 1, is_generic = false
    (Constr(194)list)
    New former:
    id = 196, level = 1, is_generic = false
    (Tuple(194(Constr(194)list)))
    New former:
    id = 197, level = 1, is_generic = false
    (Constr(194)list)
    New variable:
    id = 198, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 199, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 200, level = 1, is_generic = false, flexibility = Flexible
    New former:
    id = 201, level = 1, is_generic = false
    (Constr(200)list)
    New former:
    id = 202, level = 1, is_generic = false
    (Tuple(200(Constr(200)list)))
    New variable:
    id = 203, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 204, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 205, level = 1, is_generic = false, flexibility = Flexible
    Instantiating: 198
    Copying 198
    Instantiated result:
    198
    Unify: 205 198
    New former:
    id = 206, level = 1, is_generic = false
    (Arrow 205 204)
    New variable:
    id = 207, level = 1, is_generic = false, flexibility = Flexible
    Instantiating: 189
    Copying 189
    Instantiated result:
    189
    Unify: 207 189
    New former:
    id = 208, level = 1, is_generic = false
    (Arrow 207(Arrow 205 204))
    Instantiating: 188
    Copying 188
    Instantiated result:
    188
    Unify: 208 188
    New variable:
    id = 209, level = 1, is_generic = false, flexibility = Flexible
    Instantiating: 199
    Copying 199
    Instantiated result:
    199
    Unify: 209 199
    New former:
    id = 210, level = 1, is_generic = false
    (Arrow 209 203)
    Instantiating: 207
    Copying 207
    Instantiated result:
    207
    Unify: 210 207
    New former:
    id = 211, level = 1, is_generic = false
    (Tuple(203 204))
    Unify: 202 211
    New former:
    id = 212, level = 1, is_generic = false
    (Constr(200)list)
    Unify: 192 212
    New former:
    id = 213, level = 1, is_generic = false
    (Tuple(209 205))
    Unify: 196 213
    Unify: 193 197
    New variable:
    id = 214, level = 1, is_generic = false, flexibility = Flexible
    New former:
    id = 215, level = 1, is_generic = false
    (Constr(214)list)
    New variable:
    id = 216, level = 1, is_generic = false, flexibility = Flexible
    New former:
    id = 217, level = 1, is_generic = false
    (Constr(216)list)
    Unify: 192 217
    Unify: 193 215
    Instantiating: 191
    Copying 191
    Instantiated result:
    191
    Unify: 193 191
    New former:
    id = 218, level = 1, is_generic = false
    (Arrow(Constr(194)list)(Constr(200)list))
    Unify: 190 218
    New former:
    id = 219, level = 1, is_generic = false
    (Arrow(Arrow 194 200)(Arrow(Constr(194)list)(Constr(200)list)))
    Unify: 208 219
    Before exit:
    Current level: 1
    Region 0
    id = 187, level = 0, is_generic = false, flexibility = Flexible
    187
    Region 1
    id = 195, level = 1, is_generic = false
    (Constr(194)list)
    id = 201, level = 1, is_generic = false
    (Constr(200)list)
    id = 200, level = 1, is_generic = false, flexibility = Flexible
    200
    id = 202, level = 1, is_generic = false
    (Tuple(200(Constr(200)list)))
    id = 201, level = 1, is_generic = false
    (Constr(200)list)
    id = 201, level = 1, is_generic = false
    (Constr(200)list)
    id = 195, level = 1, is_generic = false
    (Constr(194)list)
    id = 210, level = 1, is_generic = false
    (Arrow 194 200)
    id = 194, level = 1, is_generic = false, flexibility = Flexible
    194
    id = 200, level = 1, is_generic = false, flexibility = Flexible
    200
    id = 202, level = 1, is_generic = false
    (Tuple(200(Constr(200)list)))
    id = 201, level = 1, is_generic = false
    (Constr(200)list)
    id = 194, level = 1, is_generic = false, flexibility = Flexible
    194
    id = 201, level = 1, is_generic = false
    (Constr(200)list)
    id = 194, level = 1, is_generic = false, flexibility = Flexible
    194
    id = 195, level = 1, is_generic = false
    (Constr(194)list)
    id = 196, level = 1, is_generic = false
    (Tuple(194(Constr(194)list)))
    id = 195, level = 1, is_generic = false
    (Constr(194)list)
    id = 196, level = 1, is_generic = false
    (Tuple(194(Constr(194)list)))
    id = 206, level = 1, is_generic = false
    (Arrow(Constr(194)list)(Constr(200)list))
    id = 206, level = 1, is_generic = false
    (Arrow(Constr(194)list)(Constr(200)list))
    id = 210, level = 1, is_generic = false
    (Arrow 194 200)
    id = 195, level = 1, is_generic = false
    (Constr(194)list)
    id = 208, level = 1, is_generic = false
    (Arrow(Arrow 194 200)(Arrow(Constr(194)list)(Constr(200)list)))
    id = 208, level = 1, is_generic = false
    (Arrow(Arrow 194 200)(Arrow(Constr(194)list)(Constr(200)list)))
    id = 200, level = 1, is_generic = false, flexibility = Flexible
    200
    id = 208, level = 1, is_generic = false
    (Arrow(Arrow 194 200)(Arrow(Constr(194)list)(Constr(200)list)))
    id = 194, level = 1, is_generic = false, flexibility = Flexible
    194
    id = 210, level = 1, is_generic = false
    (Arrow 194 200)
    id = 195, level = 1, is_generic = false
    (Constr(194)list)
    id = 206, level = 1, is_generic = false
    (Arrow(Constr(194)list)(Constr(200)list))
    id = 195, level = 1, is_generic = false
    (Constr(194)list)
    Array order:
    195,206,195,210,194,208,200,208,208,195,210,206,206,196,195,196,195,194,201,194,201,202,200,194,210,195,201,201,202,200,201,195
    is young? 195 = true
    is young? 194 = true
    is young? 206 = true
    is young? 201 = true
    is young? 200 = true
    is young? 210 = true
    is young? 208 = true
    is young? 196 = true
    is young? 202 = true
    Generalizing 195
    Generalizing 201
    Generalizing 200
    Generalizing 202
    Generalizing 201
    Generalizing 201
    Generalizing 195
    Generalizing 210
    Generalizing 194
    Generalizing 200
    Generalizing 202
    Generalizing 201
    Generalizing 194
    Generalizing 201
    Generalizing 194
    Generalizing 195
    Generalizing 196
    Generalizing 195
    Generalizing 196
    Generalizing 206
    Generalizing 206
    Generalizing 210
    Generalizing 195
    Generalizing 208
    Generalizing 208
    Generalizing 200
    Generalizing 208
    Generalizing 194
    Generalizing 210
    Generalizing 195
    Generalizing 206
    Generalizing 195
    After exit:
    Current level: 0
    Region 0
    id = 187, level = 0, is_generic = false, flexibility = Flexible
    187
    Region 1
    New variable:
    id = 220, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 221, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 222, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 223, level = 1, is_generic = false, flexibility = Flexible
    New former:
    id = 224, level = 1, is_generic = false
    (Constr()int)
    Unify: 223 224
    New former:
    id = 225, level = 1, is_generic = false
    (Arrow(Constr()int)222)
    New variable:
    id = 226, level = 1, is_generic = false, flexibility = Flexible
    Instantiating: 221
    Copying 221
    Instantiated result:
    221
    Unify: 226 221
    New former:
    id = 227, level = 1, is_generic = false
    (Arrow 226(Arrow(Constr()int)222))
    New former:
    id = 228, level = 1, is_generic = false
    (Constr()int)
    New former:
    id = 229, level = 1, is_generic = false
    (Constr()int)
    New former:
    id = 230, level = 1, is_generic = false
    (Constr()int)
    New former:
    id = 231, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    New former:
    id = 232, level = 1, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    Unify: 227 232
    New former:
    id = 233, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    Unify: 220 233
    Before exit:
    Current level: 1
    Region 0
    id = 187, level = 0, is_generic = false, flexibility = Flexible
    187
    Region 1
    id = 220, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    id = 225, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    id = 223, level = 1, is_generic = false
    (Constr()int)
    id = 223, level = 1, is_generic = false
    (Constr()int)
    id = 226, level = 1, is_generic = false
    (Constr()int)
    id = 227, level = 1, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 220, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    id = 225, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    id = 223, level = 1, is_generic = false
    (Constr()int)
    id = 222, level = 1, is_generic = false
    (Constr()int)
    id = 226, level = 1, is_generic = false
    (Constr()int)
    id = 226, level = 1, is_generic = false
    (Constr()int)
    id = 227, level = 1, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 222, level = 1, is_generic = false
    (Constr()int)
    Region 2
    Array order:
    222,227,226,226,222,223,225,220,227,226,223,223,225,220
    is young? 222 = true
    is young? 227 = true
    is young? 225 = true
    is young? 223 = true
    is young? 226 = true
    is young? 220 = true
    After exit:
    Current level: 0
    Region 0
    id = 225, level = 0, is_generic = true
    (Arrow(Constr()int)(Constr()int))
    id = 223, level = 0, is_generic = true
    (Constr()int)
    id = 187, level = 0, is_generic = false, flexibility = Flexible
    187
    id = 226, level = 0, is_generic = true
    (Constr()int)
    id = 227, level = 0, is_generic = true
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 220, level = 0, is_generic = true
    (Arrow(Constr()int)(Constr()int))
    id = 222, level = 0, is_generic = true
    (Constr()int)
    Region 1
    Region 2
    New variable:
    id = 234, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 235, level = 0, is_generic = false, flexibility = Flexible
    New former:
    id = 236, level = 0, is_generic = false
    (Constr(235)list)
    Unify: 234 236
    New former:
    id = 237, level = 0, is_generic = false
    (Arrow(Constr(235)list)187)
    New variable:
    id = 238, level = 0, is_generic = false, flexibility = Flexible
    Instantiating: 220
    Copying 220
    220 is generic
    New variable:
    id = 239, level = 0, is_generic = false, flexibility = Flexible
    Productive_view_map copy
    Copying 226
    226 is generic
    New variable:
    id = 240, level = 0, is_generic = false, flexibility = Flexible
    Productive_view_map copy
    Copying 222
    222 is generic
    New variable:
    id = 241, level = 0, is_generic = false, flexibility = Flexible
    Productive_view_map copy
    Instantiated result:
    (Arrow(Constr()int)(Constr()int))
    Unify: 238 239
    New former:
    id = 242, level = 0, is_generic = false
    (Arrow(Arrow(Constr()int)(Constr()int))(Arrow(Constr(235)list)187))
    Instantiating: 208
    Copying 208
    208 is generic
    New variable:
    id = 243, level = 0, is_generic = false, flexibility = Flexible
    Productive_view_map copy
    Copying 210
    210 is generic
    New variable:
    id = 244, level = 0, is_generic = false, flexibility = Flexible
    Productive_view_map copy
    Copying 194
    194 is generic
    New variable:
    id = 245, level = 0, is_generic = false, flexibility = Flexible
    Copying 200
    200 is generic
    New variable:
    id = 246, level = 0, is_generic = false, flexibility = Flexible
    Copying 206
    206 is generic
    New variable:
    id = 247, level = 0, is_generic = false, flexibility = Flexible
    Productive_view_map copy
    Copying 195
    195 is generic
    New variable:
    id = 248, level = 0, is_generic = false, flexibility = Flexible
    Productive_view_map copy
    Copying 194
    194 is generic
    Copying 201
    201 is generic
    New variable:
    id = 249, level = 0, is_generic = false, flexibility = Flexible
    Productive_view_map copy
    Copying 200
    200 is generic
    Instantiated result:
    (Arrow(Arrow 245 246)(Arrow(Constr(245)list)(Constr(246)list)))
    Unify: 242 243
    Before exit:
    Current level: 0
    Region 0
    id = 235, level = 0, is_generic = false
    (Constr()int)
    id = 238, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    id = 241, level = 0, is_generic = false
    (Constr()int)
    id = 241, level = 0, is_generic = false
    (Constr()int)
    id = 220, level = 0, is_generic = true
    (Arrow(Constr()int)(Constr()int))
    id = 225, level = 0, is_generic = true
    (Arrow(Constr()int)(Constr()int))
    id = 237, level = 0, is_generic = false
    (Arrow(Constr((Constr()int))list)(Constr((Constr()int))list))
    id = 242, level = 0, is_generic = false
    (Arrow(Arrow(Constr()int)(Constr()int))(Arrow(Constr((Constr()int))list)(Constr((Constr()int))list)))
    id = 237, level = 0, is_generic = false
    (Arrow(Constr((Constr()int))list)(Constr((Constr()int))list))
    id = 235, level = 0, is_generic = false
    (Constr()int)
    id = 234, level = 0, is_generic = false
    (Constr((Constr()int))list)
    id = 223, level = 0, is_generic = true
    (Constr()int)
    id = 187, level = 0, is_generic = false
    (Constr((Constr()int))list)
    id = 238, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    id = 242, level = 0, is_generic = false
    (Arrow(Arrow(Constr()int)(Constr()int))(Arrow(Constr((Constr()int))list)(Constr((Constr()int))list)))
    id = 226, level = 0, is_generic = true
    (Constr()int)
    id = 235, level = 0, is_generic = false
    (Constr()int)
    id = 227, level = 0, is_generic = true
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 222, level = 0, is_generic = true
    (Constr()int)
    id = 234, level = 0, is_generic = false
    (Constr((Constr()int))list)
    id = 187, level = 0, is_generic = false
    (Constr((Constr()int))list)
    Region 1
    Region 2
    Array order:
    187,234,222,227,235,226,242,238,187,223,234,235,237,242,237,225,220,241,241,238,235
    is young? 187 = true
    is young? 241 = true
    is young? 234 = true
    is young? 235 = true
    is young? 222 = true
    is young? 227 = true
    is young? 225 = true
    is young? 223 = true
    is young? 226 = true
    is young? 242 = true
    is young? 237 = true
    is young? 238 = true
    is young? 220 = true
    Generalizing 235
    Generalizing 238
    Generalizing 241
    Generalizing 241
    Generalizing 220
    Generalizing 225
    Generalizing 237
    Generalizing 242
    Generalizing 237
    Generalizing 235
    Generalizing 234
    Generalizing 223
    Generalizing 187
    Generalizing 238
    Generalizing 242
    Generalizing 226
    Generalizing 235
    Generalizing 227
    Generalizing 222
    Generalizing 234
    Generalizing 187
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
                   └──Variables: α200,α194
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: α194
                            └──Type expr: Variable: α200
                         └──Type expr: Arrow
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: α194
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: α200
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Variable: α194
                               └──Type expr: Variable: α200
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: α194
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: α200
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: α194
                                  └──Desc: Variable: xs
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: α200
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Variable: α194
                                        └──Desc: Variable
                                           └──Variable: xs
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: α194
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: α194
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α194
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: α200
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α200
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: α194
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: α194
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: α194
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α194
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: α194
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α194
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Variable: α194
                                                          └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: α194
                                                          └──Desc: Variable: xs
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: α200
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: α200
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: α200
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α200
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: α200
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α200
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Variable: α200
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: α194
                                                                   └──Type expr: Variable: α200
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Variable: α194
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: α200
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: α194
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: α200
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Variable: α194
                                                                            └──Type expr: Variable: α200
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: α194
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: α200
                                                                      └──Desc: Variable
                                                                         └──Variable: map
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: α194
                                                                         └──Type expr: Variable: α200
                                                                      └──Desc: Variable
                                                                         └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: α194
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
  print_infer_result ~abbrev_ctx:Abbreviations.Ctx.empty ~env exp;
  [%expect
    {|
    New variable:
    id = 250, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 251, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 252, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 253, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 254, level = 1, is_generic = false, flexibility = Flexible
    Instantiating: 253
    Copying 253
    Instantiated result:
    253
    Unify: 254 253
    New former:
    id = 255, level = 1, is_generic = false
    (Arrow 254 254)
    Unify: 251 255
    New variable:
    id = 256, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 257, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 258, level = 1, is_generic = false, flexibility = Flexible
    New former:
    id = 259, level = 1, is_generic = false
    (Constr()int)
    Instantiating: 256
    Copying 256
    Instantiated result:
    256
    Unify: 259 256
    Unify: 258 259
    New former:
    id = 260, level = 1, is_generic = false
    (Arrow(Constr()int)257)
    Instantiating: 251
    Copying 251
    Instantiated result:
    (Arrow 254 254)
    Unify: 260 251
    New former:
    id = 261, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    Unify: 252 261
    Before exit:
    Current level: 1
    Region 0
    id = 250, level = 0, is_generic = false, flexibility = Flexible
    250
    Region 1
    id = 252, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    id = 260, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    id = 252, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    id = 257, level = 1, is_generic = false
    (Constr()int)
    id = 257, level = 1, is_generic = false
    (Constr()int)
    id = 260, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    id = 257, level = 1, is_generic = false
    (Constr()int)
    Array order:
    257,260,257,257,252,260,252
    is young? 257 = true
    is young? 260 = true
    is young? 252 = true
    After exit:
    Current level: 0
    Region 0
    id = 260, level = 0, is_generic = true
    (Arrow(Constr()int)(Constr()int))
    id = 252, level = 0, is_generic = true
    (Arrow(Constr()int)(Constr()int))
    id = 250, level = 0, is_generic = false, flexibility = Flexible
    250
    id = 257, level = 0, is_generic = true
    (Constr()int)
    Region 1
    Instantiating: 260
    Copying 260
    260 is generic
    New variable:
    id = 262, level = 0, is_generic = false, flexibility = Flexible
    Productive_view_map copy
    Copying 257
    257 is generic
    New variable:
    id = 263, level = 0, is_generic = false, flexibility = Flexible
    Productive_view_map copy
    Copying 257
    257 is generic
    Instantiated result:
    (Arrow(Constr()int)(Constr()int))
    Unify: 250 262
    Before exit:
    Current level: 0
    Region 0
    id = 252, level = 0, is_generic = true
    (Arrow(Constr()int)(Constr()int))
    id = 260, level = 0, is_generic = true
    (Arrow(Constr()int)(Constr()int))
    id = 263, level = 0, is_generic = false
    (Constr()int)
    id = 250, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    id = 257, level = 0, is_generic = true
    (Constr()int)
    id = 250, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    Region 1
    Array order:
    250,257,250,263,260,252
    is young? 250 = true
    is young? 263 = true
    is young? 257 = true
    is young? 260 = true
    is young? 252 = true
    Generalizing 252
    Generalizing 260
    Generalizing 263
    Generalizing 250
    Generalizing 257
    Generalizing 250
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
  print_infer_result ~abbrev_ctx:Abbreviations.Ctx.empty ~env:Env.empty exp;
  [%expect
    {|
    New variable:
    id = 264, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 265, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 266, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 267, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 268, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 269, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 270, level = 1, is_generic = false, flexibility = Flexible
    New former:
    id = 271, level = 1, is_generic = false
    (Constr()int)
    Unify: 270 271
    New former:
    id = 272, level = 1, is_generic = false
    (Arrow(Constr()int)269)
    New variable:
    id = 273, level = 1, is_generic = false, flexibility = Flexible
    Instantiating: 267
    Copying 267
    Instantiated result:
    267
    Unify: 273 267
    New former:
    id = 274, level = 1, is_generic = false
    (Arrow 273(Arrow(Constr()int)269))
    New former:
    id = 275, level = 1, is_generic = false
    (Constr()int)
    New former:
    id = 276, level = 1, is_generic = false
    (Constr()int)
    New former:
    id = 277, level = 1, is_generic = false
    (Constr()int)
    New former:
    id = 278, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    New former:
    id = 279, level = 1, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    Unify: 274 279
    New former:
    id = 280, level = 1, is_generic = false
    (Arrow(Constr()int)268)
    Instantiating: 266
    Copying 266
    Instantiated result:
    266
    Unify: 280 266
    New former:
    id = 281, level = 1, is_generic = false
    (Constr()bool)
    Unify: 268 281
    New former:
    id = 282, level = 1, is_generic = false
    (Constr()bool)
    New variable:
    id = 283, level = 1, is_generic = false, flexibility = Flexible
    New former:
    id = 284, level = 1, is_generic = false
    (Constr()int)
    Unify: 283 284
    New former:
    id = 285, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()bool))
    New variable:
    id = 286, level = 1, is_generic = false, flexibility = Flexible
    Instantiating: 273
    Copying 273
    Instantiated result:
    (Constr()int)
    Unify: 286 273
    New former:
    id = 287, level = 1, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    New former:
    id = 288, level = 1, is_generic = false
    (Constr()int)
    New former:
    id = 289, level = 1, is_generic = false
    (Constr()int)
    New former:
    id = 290, level = 1, is_generic = false
    (Constr()bool)
    New former:
    id = 291, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()bool))
    New former:
    id = 292, level = 1, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    Unify: 287 292
    New former:
    id = 293, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()bool))
    Unify: 265 293
    New variable:
    id = 294, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 295, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 296, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 297, level = 1, is_generic = false, flexibility = Flexible
    New former:
    id = 298, level = 1, is_generic = false
    (Constr()int)
    Unify: 297 298
    New former:
    id = 299, level = 1, is_generic = false
    (Arrow(Constr()int)296)
    New variable:
    id = 300, level = 1, is_generic = false, flexibility = Flexible
    Instantiating: 294
    Copying 294
    Instantiated result:
    294
    Unify: 300 294
    New former:
    id = 301, level = 1, is_generic = false
    (Arrow 300(Arrow(Constr()int)296))
    New former:
    id = 302, level = 1, is_generic = false
    (Constr()int)
    New former:
    id = 303, level = 1, is_generic = false
    (Constr()int)
    New former:
    id = 304, level = 1, is_generic = false
    (Constr()int)
    New former:
    id = 305, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    New former:
    id = 306, level = 1, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    Unify: 301 306
    New former:
    id = 307, level = 1, is_generic = false
    (Arrow(Constr()int)295)
    Instantiating: 265
    Copying 265
    Instantiated result:
    (Arrow(Constr()int)(Constr()bool))
    Unify: 307 265
    New former:
    id = 308, level = 1, is_generic = false
    (Constr()bool)
    Unify: 295 308
    New former:
    id = 309, level = 1, is_generic = false
    (Constr()bool)
    New variable:
    id = 310, level = 1, is_generic = false, flexibility = Flexible
    New former:
    id = 311, level = 1, is_generic = false
    (Constr()int)
    Unify: 310 311
    New former:
    id = 312, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()bool))
    New variable:
    id = 313, level = 1, is_generic = false, flexibility = Flexible
    Instantiating: 300
    Copying 300
    Instantiated result:
    (Constr()int)
    Unify: 313 300
    New former:
    id = 314, level = 1, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    New former:
    id = 315, level = 1, is_generic = false
    (Constr()int)
    New former:
    id = 316, level = 1, is_generic = false
    (Constr()int)
    New former:
    id = 317, level = 1, is_generic = false
    (Constr()bool)
    New former:
    id = 318, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()bool))
    New former:
    id = 319, level = 1, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    Unify: 314 319
    New former:
    id = 320, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()bool))
    Unify: 280 320
    Before exit:
    Current level: 1
    Region 0
    id = 264, level = 0, is_generic = false, flexibility = Flexible
    264
    Region 1
    id = 269, level = 1, is_generic = false
    (Constr()int)
    id = 280, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()bool))
    id = 297, level = 1, is_generic = false
    (Constr()int)
    id = 312, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()bool))
    id = 307, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()bool))
    id = 296, level = 1, is_generic = false
    (Constr()int)
    id = 287, level = 1, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    id = 299, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    id = 309, level = 1, is_generic = false
    (Constr()bool)
    id = 283, level = 1, is_generic = false
    (Constr()int)
    id = 301, level = 1, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 307, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()bool))
    id = 282, level = 1, is_generic = false
    (Constr()bool)
    id = 280, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()bool))
    id = 285, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()bool))
    id = 310, level = 1, is_generic = false
    (Constr()int)
    id = 297, level = 1, is_generic = false
    (Constr()int)
    id = 296, level = 1, is_generic = false
    (Constr()int)
    id = 299, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    id = 309, level = 1, is_generic = false
    (Constr()bool)
    id = 274, level = 1, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 270, level = 1, is_generic = false
    (Constr()int)
    id = 314, level = 1, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    id = 269, level = 1, is_generic = false
    (Constr()int)
    id = 295, level = 1, is_generic = false
    (Constr()bool)
    id = 314, level = 1, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    id = 272, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()int))
    id = 269, level = 1, is_generic = false
    (Constr()int)
    id = 295, level = 1, is_generic = false
    (Constr()bool)
    id = 295, level = 1, is_generic = false
    (Constr()bool)
    id = 269, level = 1, is_generic = false
    (Constr()int)
    id = 269, level = 1, is_generic = false
    (Constr()int)
    id = 310, level = 1, is_generic = false
    (Constr()int)
    id = 301, level = 1, is_generic = false
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 296, level = 1, is_generic = false
    (Constr()int)
    id = 312, level = 1, is_generic = false
    (Arrow(Constr()int)(Constr()bool))
    id = 310, level = 1, is_generic = false
    (Constr()int)
    Array order:
    310,312,296,301,310,269,269,295,295,269,272,314,295,269,314,270,274,309,299,296,297,310,285,280,282,307,301,283,309,299,287,296,307,312,297,280,269
    is young? 310 = true
    is young? 312 = true
    is young? 309 = true
    is young? 296 = true
    is young? 301 = true
    is young? 299 = true
    is young? 297 = true
    is young? 269 = true
    is young? 295 = true
    is young? 272 = true
    is young? 270 = true
    is young? 314 = true
    is young? 274 = true
    is young? 285 = true
    is young? 282 = true
    is young? 283 = true
    is young? 280 = true
    is young? 307 = true
    is young? 287 = true
    After exit:
    Current level: 0
    Region 0
    id = 297, level = 0, is_generic = true
    (Constr()int)
    id = 312, level = 0, is_generic = true
    (Arrow(Constr()int)(Constr()bool))
    id = 274, level = 0, is_generic = true
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 307, level = 0, is_generic = true
    (Arrow(Constr()int)(Constr()bool))
    id = 296, level = 0, is_generic = true
    (Constr()int)
    id = 270, level = 0, is_generic = true
    (Constr()int)
    id = 287, level = 0, is_generic = true
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    id = 299, level = 0, is_generic = true
    (Arrow(Constr()int)(Constr()int))
    id = 309, level = 0, is_generic = true
    (Constr()bool)
    id = 283, level = 0, is_generic = true
    (Constr()int)
    id = 314, level = 0, is_generic = true
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    id = 272, level = 0, is_generic = true
    (Arrow(Constr()int)(Constr()int))
    id = 282, level = 0, is_generic = true
    (Constr()bool)
    id = 269, level = 0, is_generic = true
    (Constr()int)
    id = 295, level = 0, is_generic = true
    (Constr()bool)
    id = 264, level = 0, is_generic = false, flexibility = Flexible
    264
    id = 280, level = 0, is_generic = true
    (Arrow(Constr()int)(Constr()bool))
    id = 285, level = 0, is_generic = true
    (Arrow(Constr()int)(Constr()bool))
    id = 310, level = 0, is_generic = true
    (Constr()int)
    id = 301, level = 0, is_generic = true
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    Region 1
    Instantiating: 307
    Copying 307
    307 is generic
    New variable:
    id = 321, level = 0, is_generic = false, flexibility = Flexible
    Productive_view_map copy
    Copying 296
    296 is generic
    New variable:
    id = 322, level = 0, is_generic = false, flexibility = Flexible
    Productive_view_map copy
    Copying 295
    295 is generic
    New variable:
    id = 323, level = 0, is_generic = false, flexibility = Flexible
    Productive_view_map copy
    Instantiated result:
    (Arrow(Constr()int)(Constr()bool))
    Unify: 264 321
    Before exit:
    Current level: 0
    Region 0
    id = 297, level = 0, is_generic = true
    (Constr()int)
    id = 312, level = 0, is_generic = true
    (Arrow(Constr()int)(Constr()bool))
    id = 274, level = 0, is_generic = true
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 307, level = 0, is_generic = true
    (Arrow(Constr()int)(Constr()bool))
    id = 296, level = 0, is_generic = true
    (Constr()int)
    id = 270, level = 0, is_generic = true
    (Constr()int)
    id = 287, level = 0, is_generic = true
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    id = 299, level = 0, is_generic = true
    (Arrow(Constr()int)(Constr()int))
    id = 309, level = 0, is_generic = true
    (Constr()bool)
    id = 283, level = 0, is_generic = true
    (Constr()int)
    id = 323, level = 0, is_generic = false
    (Constr()bool)
    id = 314, level = 0, is_generic = true
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()bool)))
    id = 264, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()bool))
    id = 272, level = 0, is_generic = true
    (Arrow(Constr()int)(Constr()int))
    id = 282, level = 0, is_generic = true
    (Constr()bool)
    id = 269, level = 0, is_generic = true
    (Constr()int)
    id = 295, level = 0, is_generic = true
    (Constr()bool)
    id = 264, level = 0, is_generic = false
    (Arrow(Constr()int)(Constr()bool))
    id = 280, level = 0, is_generic = true
    (Arrow(Constr()int)(Constr()bool))
    id = 285, level = 0, is_generic = true
    (Arrow(Constr()int)(Constr()bool))
    id = 310, level = 0, is_generic = true
    (Constr()int)
    id = 301, level = 0, is_generic = true
    (Arrow(Constr()int)(Arrow(Constr()int)(Constr()int)))
    id = 322, level = 0, is_generic = false
    (Constr()int)
    Region 1
    Array order:
    322,301,310,285,280,264,295,269,282,272,264,314,323,283,309,299,287,270,296,307,274,312,297
    is young? 322 = true
    is young? 301 = true
    is young? 299 = true
    is young? 296 = true
    is young? 297 = true
    is young? 269 = true
    is young? 310 = true
    is young? 285 = true
    is young? 282 = true
    is young? 283 = true
    is young? 280 = true
    is young? 295 = true
    is young? 264 = true
    is young? 323 = true
    is young? 272 = true
    is young? 270 = true
    is young? 314 = true
    is young? 312 = true
    is young? 309 = true
    is young? 287 = true
    is young? 307 = true
    is young? 274 = true
    Generalizing 297
    Generalizing 312
    Generalizing 274
    Generalizing 307
    Generalizing 296
    Generalizing 270
    Generalizing 287
    Generalizing 299
    Generalizing 309
    Generalizing 283
    Generalizing 323
    Generalizing 314
    Generalizing 264
    Generalizing 272
    Generalizing 282
    Generalizing 269
    Generalizing 295
    Generalizing 264
    Generalizing 280
    Generalizing 285
    Generalizing 310
    Generalizing 301
    Generalizing 322
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
  print_infer_result ~abbrev_ctx:Abbreviations.Ctx.empty ~env:Env.empty exp;
  [%expect
    {|
    New variable:
    id = 324, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 325, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 326, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 327, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 328, level = 1, is_generic = false, flexibility = Flexible
    New former:
    id = 329, level = 1, is_generic = false
    (Constr()int)
    Unify: 328 329
    New former:
    id = 330, level = 1, is_generic = false
    (Arrow 327(Constr()int))
    Unify: 325 330
    New variable:
    id = 331, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 332, level = 1, is_generic = false, flexibility = Flexible
    New former:
    id = 333, level = 1, is_generic = false
    (Constr()bool)
    Unify: 332 333
    New former:
    id = 334, level = 1, is_generic = false
    (Arrow 331(Constr()bool))
    Unify: 326 334
    Before exit:
    Current level: 1
    Region 0
    id = 324, level = 0, is_generic = false, flexibility = Flexible
    324
    Region 1
    id = 327, level = 1, is_generic = false, flexibility = Flexible
    327
    id = 328, level = 1, is_generic = false
    (Constr()int)
    id = 332, level = 1, is_generic = false
    (Constr()bool)
    id = 332, level = 1, is_generic = false
    (Constr()bool)
    id = 325, level = 1, is_generic = false
    (Arrow 327(Constr()int))
    id = 331, level = 1, is_generic = false, flexibility = Flexible
    331
    id = 326, level = 1, is_generic = false
    (Arrow 331(Constr()bool))
    id = 326, level = 1, is_generic = false
    (Arrow 331(Constr()bool))
    Array order:
    326,326,331,325,332,332,328,327
    is young? 326 = true
    is young? 332 = true
    is young? 331 = true
    is young? 325 = true
    is young? 328 = true
    is young? 327 = true
    Generalizing 327
    Generalizing 325
    Generalizing 331
    Generalizing 326
    Generalizing 326
    After exit:
    Current level: 0
    Region 0
    id = 324, level = 0, is_generic = false, flexibility = Flexible
    324
    id = 328, level = 0, is_generic = true
    (Constr()int)
    id = 332, level = 0, is_generic = true
    (Constr()bool)
    Region 1
    Instantiating: 325
    Copying 325
    325 is generic
    New variable:
    id = 335, level = 0, is_generic = false, flexibility = Flexible
    Productive_view_map copy
    Copying 327
    327 is generic
    New variable:
    id = 336, level = 0, is_generic = false, flexibility = Flexible
    Copying 328
    328 is generic
    New variable:
    id = 337, level = 0, is_generic = false, flexibility = Flexible
    Productive_view_map copy
    Instantiated result:
    (Arrow 336(Constr()int))
    Unify: 324 335
    Before exit:
    Current level: 0
    Region 0
    id = 324, level = 0, is_generic = false
    (Arrow 336(Constr()int))
    id = 324, level = 0, is_generic = false
    (Arrow 336(Constr()int))
    id = 336, level = 0, is_generic = false, flexibility = Flexible
    336
    id = 337, level = 0, is_generic = false
    (Constr()int)
    id = 328, level = 0, is_generic = true
    (Constr()int)
    id = 332, level = 0, is_generic = true
    (Constr()bool)
    Region 1
    Array order:
    332,328,337,336,324,324
    is young? 332 = true
    is young? 328 = true
    is young? 337 = true
    is young? 336 = true
    is young? 324 = true
    Generalizing 324
    Generalizing 324
    Generalizing 336
    Generalizing 337
    Generalizing 328
    Generalizing 332
    After exit:
    Current level: -1
    Region 0
    Region 1
    Variables: α336
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Variable: α336
          └──Type expr: Constructor: int
       └──Desc: Let rec
          └──Value bindings:
             └──Value binding:
                └──Variable: bar
                └──Abstraction:
                   └──Variables: α331
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: α327
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: α327
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Constant: 1
             └──Value binding:
                └──Variable: foo
                └──Abstraction:
                   └──Variables: α327
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: α331
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: α331
                            └──Desc: Variable: y
                         └──Expression:
                            └──Type expr: Constructor: bool
                            └──Desc: Constant: true
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Variable: α336
                └──Type expr: Constructor: int
             └──Desc: Variable
                └──Variable: foo
                └──Type expr: Variable: α336 |}]

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
  print_infer_result ~abbrev_ctx:Abbreviations.Ctx.empty ~env:Env.empty exp;
  [%expect
    {|
    New variable:
    id = 338, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 339, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 340, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 341, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 342, level = 1, is_generic = false, flexibility = Flexible
    Instantiating: 341
    Copying 341
    Instantiated result:
    341
    Unify: 342 341
    New former:
    id = 343, level = 1, is_generic = false
    (Arrow 342 342)
    Unify: 340 343
    New former:
    id = 344, level = 1, is_generic = false
    (Arrow(Arrow 342 342)339)
    New variable:
    id = 345, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 346, level = 1, is_generic = false, flexibility = Flexible
    New former:
    id = 347, level = 1, is_generic = false
    (Constr()unit)
    Unify: 346 347
    New former:
    id = 348, level = 1, is_generic = false
    (Arrow 345(Constr()unit))
    Unify: 344 348
    Before exit:
    Current level: 1
    Region 0
    id = 338, level = 0, is_generic = false, flexibility = Flexible
    338
    Region 1
    id = 339, level = 1, is_generic = false
    (Constr()unit)
    id = 340, level = 1, is_generic = false
    (Arrow 342 342)
    id = 339, level = 1, is_generic = false
    (Constr()unit)
    id = 344, level = 1, is_generic = false
    (Arrow(Arrow 342 342)(Constr()unit))
    id = 340, level = 1, is_generic = false
    (Arrow 342 342)
    id = 342, level = 1, is_generic = false, flexibility = Flexible
    342
    id = 344, level = 1, is_generic = false
    (Arrow(Arrow 342 342)(Constr()unit))
    Array order:
    344,342,340,344,339,340,339
    is young? 344 = true
    is young? 339 = true
    is young? 340 = true
    is young? 342 = true
    Generalizing 340
    Generalizing 344
    Generalizing 340
    Generalizing 342
    Generalizing 344
    After exit:
    Current level: 0
    Region 0
    id = 339, level = 0, is_generic = true
    (Constr()unit)
    id = 338, level = 0, is_generic = false, flexibility = Flexible
    338
    Region 1
    Instantiating: 339
    Copying 339
    339 is generic
    New variable:
    id = 349, level = 0, is_generic = false, flexibility = Flexible
    Productive_view_map copy
    Instantiated result:
    (Constr()unit)
    Unify: 338 349
    Before exit:
    Current level: 0
    Region 0
    id = 338, level = 0, is_generic = false
    (Constr()unit)
    id = 339, level = 0, is_generic = true
    (Constr()unit)
    id = 338, level = 0, is_generic = false
    (Constr()unit)
    Region 1
    Array order:
    338,339,338
    is young? 338 = true
    is young? 339 = true
    Generalizing 338
    Generalizing 339
    Generalizing 338
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
                   └──Variables: α342
                   └──Expression:
                      └──Type expr: Constructor: unit
                      └──Desc: Application
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: α342
                                  └──Type expr: Variable: α342
                               └──Type expr: Constructor: unit
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: α342
                                     └──Type expr: Variable: α342
                                  └──Desc: Variable: f
                               └──Expression:
                                  └──Type expr: Constructor: unit
                                  └──Desc: Constant: ()
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: α342
                               └──Type expr: Variable: α342
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: α342
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Variable: α342
                                  └──Desc: Variable
                                     └──Variable: x
          └──Expression:
             └──Type expr: Constructor: unit
             └──Desc: Variable
                └──Variable: u |}]

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
    New variable:
    id = 350, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 351, level = 1, is_generic = false, flexibility = Flexible
    New former:
    id = 352, level = 1, is_generic = false
    (Constr()int)
    New former:
    id = 353, level = 1, is_generic = false
    (Constr((Constr()int))G)
    New variable:
    id = 354, level = 1, is_generic = false, flexibility = Flexible
    New variable:
    id = 355, level = 1, is_generic = false, flexibility = Flexible
    Instantiating: 354
    Copying 354
    Instantiated result:
    354
    Unify: 355 354
    New former:
    id = 356, level = 1, is_generic = false
    (Arrow 355 355)
    Unify: 353 356
    Expanding
    Expanded!
    Expanding
    Expanded!
    Unify: 351 353
    Before exit:
    Current level: 1
    Region 0
    id = 350, level = 0, is_generic = false, flexibility = Flexible
    350
    Region 1
    id = 358, level = 1, is_generic = false
    (Constr((Constr()int))K)
    id = 351, level = 1, is_generic = false
    (Arrow(Constr((Constr()int))K)(Constr((Constr()int))K))
    id = 351, level = 1, is_generic = false
    (Arrow(Constr((Constr()int))K)(Constr((Constr()int))K))
    id = 351, level = 1, is_generic = false
    (Arrow(Constr((Constr()int))K)(Constr((Constr()int))K))
    id = 358, level = 1, is_generic = false
    (Constr((Constr()int))K)
    id = 352, level = 1, is_generic = false
    (Constr()int)
    Array order:
    352,358,351,351,351,358
    is young? 352 = true
    is young? 358 = true
    is young? 351 = true
    After exit:
    Current level: 0
    Region 0
    id = 351, level = 0, is_generic = true
    (Arrow(Constr((Constr()int))K)(Constr((Constr()int))K))
    id = 358, level = 0, is_generic = true
    (Constr((Constr()int))K)
    id = 350, level = 0, is_generic = false, flexibility = Flexible
    350
    id = 352, level = 0, is_generic = true
    (Constr()int)
    Region 1
    New variable:
    id = 360, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 361, level = 0, is_generic = false, flexibility = Flexible
    New variable:
    id = 362, level = 0, is_generic = false, flexibility = Flexible
    New former:
    id = 363, level = 0, is_generic = false
    (Constr(360)K)
    New variable:
    id = 364, level = 0, is_generic = false, flexibility = Flexible
    Instantiating: 363
    Copying 363
    Instantiated result:
    (Constr(360)K)
    Unify: 364 363
    New former:
    id = 365, level = 0, is_generic = false
    (Arrow(Constr(360)K)362)
    Instantiating: 351
    Copying 351
    351 is generic
    New variable:
    id = 366, level = 0, is_generic = false, flexibility = Flexible
    Productive_view_map copy
    Copying 358
    358 is generic
    New variable:
    id = 367, level = 0, is_generic = false, flexibility = Flexible
    Productive_view_map copy
    Copying 352
    352 is generic
    New variable:
    id = 368, level = 0, is_generic = false, flexibility = Flexible
    Productive_view_map copy
    Copying 358
    358 is generic
    Productive_view_map copy
    Copying 358
    358 is generic
    Productive_view_map copy
    Copying 352
    352 is generic
    Instantiated result:
    (Arrow(Constr((Constr()int))K)(Constr((Constr()int))K))
    Unify: 365 366
    Unify: 361 362
    New former:
    id = 369, level = 0, is_generic = false
    (Arrow(Constr((Constr()int))K)(Constr((Constr()int))K))
    Unify: 350 369
    Before exit:
    Current level: 0
    Region 0
    id = 350, level = 0, is_generic = false
    (Arrow(Constr((Constr()int))K)(Constr((Constr()int))K))
    id = 360, level = 0, is_generic = false
    (Constr()int)
    id = 361, level = 0, is_generic = false
    (Constr((Constr()int))K)
    id = 361, level = 0, is_generic = false
    (Constr((Constr()int))K)
    id = 351, level = 0, is_generic = true
    (Arrow(Constr((Constr()int))K)(Constr((Constr()int))K))
    id = 365, level = 0, is_generic = false
    (Arrow(Constr((Constr()int))K)(Constr((Constr()int))K))
    id = 361, level = 0, is_generic = false
    (Constr((Constr()int))K)
    id = 361, level = 0, is_generic = false
    (Constr((Constr()int))K)
    id = 365, level = 0, is_generic = false
    (Arrow(Constr((Constr()int))K)(Constr((Constr()int))K))
    id = 350, level = 0, is_generic = false
    (Arrow(Constr((Constr()int))K)(Constr((Constr()int))K))
    id = 361, level = 0, is_generic = false
    (Constr((Constr()int))K)
    id = 358, level = 0, is_generic = true
    (Constr((Constr()int))K)
    id = 360, level = 0, is_generic = false
    (Constr()int)
    id = 352, level = 0, is_generic = true
    (Constr()int)
    Region 1
    Array order:
    352,360,358,361,350,365,361,361,365,351,361,361,360,350
    is young? 352 = true
    is young? 360 = true
    is young? 358 = true
    is young? 361 = true
    is young? 350 = true
    is young? 365 = true
    is young? 351 = true
    Generalizing 350
    Generalizing 360
    Generalizing 361
    Generalizing 361
    Generalizing 351
    Generalizing 365
    Generalizing 361
    Generalizing 361
    Generalizing 365
    Generalizing 350
    Generalizing 361
    Generalizing 358
    Generalizing 360
    Generalizing 352
    After exit:
    Current level: -1
    Region 0
    Region 1
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
                            └──Variable: x |}]