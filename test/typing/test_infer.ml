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
          , Pexp_fun (Ppat_var "y", Pexp_app (Pexp_var "f", Pexp_var "x")) ) )
  in
  (* print_constraint_result ~env:Env.empty exp; *)
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
    Variables: α70,α69,α72
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Arrow
             └──Type expr: Variable: α72
             └──Type expr: Variable: α70
          └──Type expr: Arrow
             └──Type expr: Variable: α72
             └──Type expr: Arrow
                └──Type expr: Variable: α69
                └──Type expr: Variable: α70
       └──Desc: Function
          └──Pattern:
             └──Type expr: Arrow
                └──Type expr: Variable: α72
                └──Type expr: Variable: α70
             └──Desc: Variable: f
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Variable: α72
                └──Type expr: Arrow
                   └──Type expr: Variable: α69
                   └──Type expr: Variable: α70
             └──Desc: Function
                └──Pattern:
                   └──Type expr: Variable: α72
                   └──Desc: Variable: x
                └──Expression:
                   └──Type expr: Arrow
                      └──Type expr: Variable: α69
                      └──Type expr: Variable: α70
                   └──Desc: Function
                      └──Pattern:
                         └──Type expr: Variable: α69
                         └──Desc: Variable: y
                      └──Expression:
                         └──Type expr: Variable: α70
                         └──Desc: Application
                            └──Expression:
                               └──Type expr: Arrow
                                  └──Type expr: Variable: α72
                                  └──Type expr: Variable: α70
                               └──Desc: Variable
                                  └──Variable: f
                            └──Expression:
                               └──Type expr: Variable: α72
                               └──Desc: Variable
                                  └──Variable: x |}]

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
    Variables: α84,α79,α86
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Arrow
             └──Type expr: Variable: α86
             └──Type expr: Arrow
                └──Type expr: Variable: α84
                └──Type expr: Variable: α79
          └──Type expr: Arrow
             └──Type expr: Tuple
                └──Type expr: Variable: α86
                └──Type expr: Variable: α84
             └──Type expr: Variable: α79
       └──Desc: Function
          └──Pattern:
             └──Type expr: Arrow
                └──Type expr: Variable: α86
                └──Type expr: Arrow
                   └──Type expr: Variable: α84
                   └──Type expr: Variable: α79
             └──Desc: Variable: f
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Tuple
                   └──Type expr: Variable: α86
                   └──Type expr: Variable: α84
                └──Type expr: Variable: α79
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
                   └──Type expr: Variable: α79
                   └──Desc: Application
                      └──Expression:
                         └──Type expr: Arrow
                            └──Type expr: Variable: α84
                            └──Type expr: Variable: α79
                         └──Desc: Application
                            └──Expression:
                               └──Type expr: Arrow
                                  └──Type expr: Variable: α86
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: α84
                                     └──Type expr: Variable: α79
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
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
    Variables: α100,α98,α96
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Arrow
             └──Type expr: Variable: α98
             └──Type expr: Variable: α96
          └──Type expr: Arrow
             └──Type expr: Arrow
                └──Type expr: Variable: α100
                └──Type expr: Variable: α98
             └──Type expr: Arrow
                └──Type expr: Variable: α100
                └──Type expr: Variable: α96
       └──Desc: Function
          └──Pattern:
             └──Type expr: Arrow
                └──Type expr: Variable: α98
                └──Type expr: Variable: α96
             └──Desc: Variable: f
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Arrow
                   └──Type expr: Variable: α100
                   └──Type expr: Variable: α98
                └──Type expr: Arrow
                   └──Type expr: Variable: α100
                   └──Type expr: Variable: α96
             └──Desc: Function
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: α100
                      └──Type expr: Variable: α98
                   └──Desc: Variable: g
                └──Expression:
                   └──Type expr: Arrow
                      └──Type expr: Variable: α100
                      └──Type expr: Variable: α96
                   └──Desc: Function
                      └──Pattern:
                         └──Type expr: Variable: α100
                         └──Desc: Variable: x
                      └──Expression:
                         └──Type expr: Variable: α96
                         └──Desc: Application
                            └──Expression:
                               └──Type expr: Arrow
                                  └──Type expr: Variable: α98
                                  └──Type expr: Variable: α96
                               └──Desc: Variable
                                  └──Variable: f
                            └──Expression:
                               └──Type expr: Variable: α98
                               └──Desc: Application
                                  └──Expression:
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: α100
                                        └──Type expr: Variable: α98
                                     └──Desc: Variable
                                        └──Variable: g
                                  └──Expression:
                                     └──Type expr: Variable: α100
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
    Variables: α105,α104
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Tuple
             └──Type expr: Variable: α104
             └──Type expr: Variable: α105
          └──Type expr: Variable: α104
       └──Desc: Function
          └──Pattern:
             └──Type expr: Tuple
                └──Type expr: Variable: α104
                └──Type expr: Variable: α105
             └──Desc: Tuple
                └──Pattern:
                   └──Type expr: Variable: α104
                   └──Desc: Variable: x
                └──Pattern:
                   └──Type expr: Variable: α105
                   └──Desc: Variable: y
          └──Expression:
             └──Type expr: Variable: α104
             └──Desc: Variable
                └──Variable: x |}]

let%expect_test "function - snd" =
  let exp =
    (* fun (x, y) -> y *)
    Pexp_fun (Ppat_tuple [ Ppat_var "x"; Ppat_var "y" ], Pexp_var "y")
  in
  (* print_constraint_result ~env:Env.empty exp; *)
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
    Variables: α111,α113
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Tuple
             └──Type expr: Variable: α113
             └──Type expr: Variable: α111
          └──Type expr: Variable: α111
       └──Desc: Function
          └──Pattern:
             └──Type expr: Tuple
                └──Type expr: Variable: α113
                └──Type expr: Variable: α111
             └──Desc: Tuple
                └──Pattern:
                   └──Type expr: Variable: α113
                   └──Desc: Variable: x
                └──Pattern:
                   └──Type expr: Variable: α111
                   └──Desc: Variable: y
          └──Expression:
             └──Type expr: Variable: α111
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
  print_infer_result ~env exp;
  [%expect
    {|
    Variables: α118
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Constructor: list
             └──Type expr: Variable: α118
          └──Type expr: Variable: α118
       └──Desc: Function
          └──Pattern:
             └──Type expr: Constructor: list
                └──Type expr: Variable: α118
             └──Desc: Construct
                └──Constructor description:
                   └──Name: Cons
                   └──Constructor argument type:
                      └──Type expr: Tuple
                         └──Type expr: Variable: α118
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: α118
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: α118
                └──Pattern:
                   └──Type expr: Tuple
                      └──Type expr: Variable: α118
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: α118
                   └──Desc: Tuple
                      └──Pattern:
                         └──Type expr: Variable: α118
                         └──Desc: Variable: x
                      └──Pattern:
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: α118
                         └──Desc: Any
          └──Expression:
             └──Type expr: Variable: α118
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
    Variables: α130
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Variable: α130
          └──Type expr: Variable: α130
       └──Desc: Function
          └──Pattern:
             └──Type expr: Variable: α130
             └──Desc: Variable: x
          └──Expression:
             └──Type expr: Variable: α130
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
    Variables: α139
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Variable: α139
          └──Type expr: Variable: α139
       └──Desc: Function
          └──Pattern:
             └──Type expr: Variable: α136
             └──Desc: Variable: x
          └──Expression:
             └──Type expr: Variable: α136
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
    ("Cannot unify types" (type_expr1 (Ttyp_constr (() int)))
     (type_expr2 (Ttyp_var "\206\177158"))) |}]

let%expect_test "let - identity" =
  let exp =
    (* let id x = x in id id () *)
    Pexp_let
      ( [ { pvb_pat = Ppat_var "id"
          ; pvb_expr = Pexp_fun (Ppat_var "x", Pexp_var "x")
          }
        ]
      , Pexp_app (Pexp_app (Pexp_var "id", Pexp_var "id"), Pexp_const Const_unit)
      )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
    Variables:
    Expression:
    └──Expression:
       └──Type expr: Constructor: unit
       └──Desc: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: α173
                      └──Type expr: Variable: α173
                   └──Desc: Variable: id
                └──Abstraction:
                   └──Variables: α173
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: α173
                         └──Type expr: Variable: α173
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: α173
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: α173
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

let%expect_test "let - map" =
  let env = add_list Env.empty in
  let exp =
    (* let rec map f xs = match xs with (Nil -> Nil | Cons (x, xs) -> Cons (f x, map f xs)) in let f x = x + 1 in map f Nil *)
    Pexp_let_rec
      ( [ { prvb_var = "map"
          ; prvb_expr =
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
          ( [ { pvb_pat = Ppat_var "f"
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
                   └──Variables: α195,α211
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: α211
                            └──Type expr: Variable: α195
                         └──Type expr: Arrow
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: α211
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: α195
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Variable: α211
                               └──Type expr: Variable: α195
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: α211
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: α195
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: α211
                                  └──Desc: Variable: xs
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: α195
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Variable: α211
                                        └──Desc: Variable
                                           └──Variable: xs
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: α211
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: α211
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α211
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: α195
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α195
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: α211
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: α211
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: α211
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α211
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: α211
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α211
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Variable: α211
                                                          └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: α211
                                                          └──Desc: Variable: xs
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: α195
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: α195
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: α195
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α195
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: α195
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: α195
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Variable: α195
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: α211
                                                                   └──Type expr: Variable: α195
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Variable: α211
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: α195
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: α211
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: α195
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Variable: α211
                                                                            └──Type expr: Variable: α195
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: α211
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: α195
                                                                      └──Desc: Variable
                                                                         └──Variable: map
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: α211
                                                                         └──Type expr: Variable: α195
                                                                      └──Desc: Variable
                                                                         └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: α211
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
    Pexp_let_rec
      ( [ { prvb_var = "id"; prvb_expr = Pexp_fun (Ppat_var "x", Pexp_var "x") }
        ; { prvb_var = "id_int"
          ; prvb_expr =
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
    Pexp_let_rec
      ( [ { prvb_var = "is_even"
          ; prvb_expr =
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
        ; { prvb_var = "is_odd"
          ; prvb_expr =
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
    Pexp_let_rec
      ( [ { prvb_var = "foo"
          ; prvb_expr = Pexp_fun (Ppat_var "x", Pexp_const (Const_int 1))
          }
        ; { prvb_var = "bar"
          ; prvb_expr = Pexp_fun (Ppat_var "y", Pexp_const (Const_bool true))
          }
        ]
      , Pexp_var "foo" )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
    Variables: α325
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Variable: α325
          └──Type expr: Constructor: int
       └──Desc: Let rec
          └──Value bindings:
             └──Value binding:
                └──Variable: bar
                └──Abstraction:
                   └──Variables: α320
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: α316
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: α316
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Constant: 1
             └──Value binding:
                └──Variable: foo
                └──Abstraction:
                   └──Variables: α316
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: α320
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: α320
                            └──Desc: Variable: y
                         └──Expression:
                            └──Type expr: Constructor: bool
                            └──Desc: Constant: true
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Variable: α325
                └──Type expr: Constructor: int
             └──Desc: Variable
                └──Variable: foo
                └──Type expr: Variable: α325 |}]

let%expect_test "f-pottier elaboration 1" =
  let exp =
    (* let u = (fun f -> ()) (fun x -> x) in u *)
    Pexp_let
      ( [ { pvb_pat = Ppat_var "u"
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
                   └──Variables: α335
                   └──Expression:
                      └──Type expr: Constructor: unit
                      └──Desc: Application
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: α335
                                  └──Type expr: Variable: α335
                               └──Type expr: Constructor: unit
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: α335
                                     └──Type expr: Variable: α335
                                  └──Desc: Variable: f
                               └──Expression:
                                  └──Type expr: Constructor: unit
                                  └──Desc: Constant: ()
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: α335
                               └──Type expr: Variable: α335
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: α335
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Variable: α335
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
      ( [ { pvb_pat = Ppat_var "coerce"
          ; pvb_expr =
              Pexp_forall
                ( [ "a"; "b" ]
                , Pexp_fun
                    ( Ppat_var "eq"
                    , Pexp_fun
                        ( Ppat_var "x"
                        , Pexp_match
                            ( Pexp_constraint
                                ( Pexp_var "eq"
                                , Ptyp_constr
                                    ([ Ptyp_var "a"; Ptyp_var "b" ], "eq") )
                            , [ { pc_lhs =
                                    Ppat_construct ("Refl", None)
                                ; pc_rhs =
                                    Pexp_coerce
                                      (Pexp_var "x", Ptyp_var "a", Ptyp_var "b")
                                }
                              ] ) ) ) )
          }
        ]
      , Pexp_const Const_unit )
  in
  (* print_constraint_result ~env exp; *)
  print_infer_result ~env exp;
  [%expect{|
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
                         └──Type expr: Variable: α355
                         └──Type expr: Variable: α356
                      └──Type expr: Arrow
                         └──Type expr: Variable: α355
                         └──Type expr: Variable: α356
                   └──Desc: Variable: coerce
                └──Abstraction:
                   └──Variables: α355,α356
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: α355
                            └──Type expr: Variable: α356
                         └──Type expr: Arrow
                            └──Type expr: Variable: α355
                            └──Type expr: Variable: α356
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: α340
                               └──Type expr: Variable: α346
                            └──Desc: Variable: eq
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: α340
                               └──Type expr: Variable: α346
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: α340
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Variable: α346
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: α340
                                           └──Type expr: Variable: α346
                                        └──Desc: Variable
                                           └──Variable: eq
                                     └──Type expr: Constructor: eq
                                        └──Type expr: Variable: α340
                                        └──Type expr: Variable: α346
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: α340
                                                 └──Type expr: Variable: α346
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Refl
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: α340
                                                          └──Type expr: Variable: α346
                                           └──Expression:
                                              └──Type expr: Variable: α346
                                              └──Desc: Variable
                                                 └──Variable: x
          └──Expression:
             └──Type expr: Constructor: unit
             └──Desc: Constant: () |}]
