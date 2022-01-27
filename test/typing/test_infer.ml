open! Import
open Parsetree
open Ast_types
open Types
module Constraint = Typing.Import.Constraint
open Constraint

let print_constraint_result ~env exp =
  let t = Infer.Expression.infer exp |> Computation.Expression.run ~env in
  let output =
    match t with
    | Ok t -> Constraint.sexp_of_t t
    | Error err -> err
  in
  output |> Sexp.to_string_hum |> print_endline


let print_solve_result ?(abbrevs = Abbreviations.empty) cst =
  Constraint.sexp_of_t cst |> Sexp.to_string_hum |> print_endline;
  match Infer.solve ~abbrevs cst with
  | Ok _ -> Format.fprintf Format.std_formatter "Constraint is true.\n"
  | Error err -> Sexp.to_string_hum err |> print_endline


let print_infer_result ~env ?(abbrevs = Abbreviations.empty) exp =
  let texp = Infer.infer ~env ~abbrevs exp in
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
          , Pexp_fun
              ( Ppat_var "y"
              , Pexp_app
                  (Pexp_var "f", Pexp_tuple [ Pexp_var "x"; Pexp_var "y" ]) ) )
      )
  in
  print_infer_result ~env:Env.empty exp;
  [%expect
    {|
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

let%expect_test "let rec - polymorphic recursion" =
  let env = add_list Env.empty in
  let exp =
    (* let rec (type a) id : a -> a = fun x -> x and id_int x = id (x : int) in id *)
    Pexp_let
      ( Recursive
      , [ { pvb_forall_vars = [ "a" ]
          ; pvb_pat =
              Ppat_constraint
                (Ppat_var "id", Ptyp_arrow (Ptyp_var "a", Ptyp_var "a"))
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
  [%expect {|
    Variables: α374
    Expression:
    └──Expression:
       └──Type expr: Arrow
          └──Type expr: Variable: α374
          └──Type expr: Variable: α374
       └──Desc: Let rec
          └──Value bindings:
             └──Value binding:
                └──Variable: id
                └──Abstraction:
                   └──Variables: α347
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: α362
                         └──Type expr: Variable: α362
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: α362
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: α362
                            └──Desc: Variable
                               └──Variable: x
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
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: id
                                     └──Type expr: Constructor: int
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: x
          └──Expression:
             └──Type expr: Arrow
                └──Type expr: Variable: α374
                └──Type expr: Variable: α374
             └──Desc: Variable
                └──Variable: id
                └──Type expr: Variable: α374 |}]

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
  (* let (type a b) coerce eq (x : a) = match (eq : (a, b) eq) with Refl -> (x : b) in () *)
  let env = add_eq Env.empty in
  let exp =
    Pexp_let
      ( Nonrecursive
      , [ { pvb_forall_vars = [ "a"; "b" ]
          ; pvb_pat = Ppat_var "coerce"
          ; pvb_expr =
              Pexp_fun
                ( Ppat_constraint
                    ( Ppat_var "eq"
                    , Ptyp_constr ([ Ptyp_var "a"; Ptyp_var "b" ], "eq") )
                , Pexp_fun
                    ( Ppat_constraint
                        (Ppat_var "x", Ptyp_constr ([ Ptyp_var "a" ], "t"))
                    , Pexp_constraint
                        ( Pexp_match
                            ( Pexp_var "eq"
                            , [ { pc_lhs = Ppat_construct ("Refl", None)
                                ; pc_rhs = Pexp_var "x"
                                }
                              ] )
                        , Ptyp_constr ([ Ptyp_var "b" ], "t") ) ) )
          }
        ]
      , Pexp_const Const_unit )
  in
  (* print_constraint_result ~env exp; *)
  print_infer_result ~env exp;
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
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: α392
                         └──Type expr: Variable: α385
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: α392
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: α385
                   └──Desc: Variable: coerce
                └──Abstraction:
                   └──Variables: α392,α385
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: α392
                            └──Type expr: Variable: α385
                         └──Type expr: Arrow
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: α392
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: α385
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: α392
                               └──Type expr: Variable: α385
                            └──Desc: Variable: eq
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: α392
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: α385
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: α392
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: α385
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: α392
                                           └──Type expr: Variable: α385
                                        └──Desc: Variable
                                           └──Variable: eq
                                     └──Type expr: Constructor: eq
                                        └──Type expr: Variable: α392
                                        └──Type expr: Variable: α385
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: α392
                                                 └──Type expr: Variable: α385
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Refl
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: α392
                                                          └──Type expr: Variable: α385
                                           └──Expression:
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: α385
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
    ((Forall (364 365))
     ((Def_poly ()) ((x 364))
      ((Implication (((Var 364) (Var 365)))) ((Instance x) 365))))
    Constraint is true. |}]

let%expect_test "abbrev - morel" =
  let abbrevs =
    let open Types.Algebra.Type_former in
    let abbrev_k =
      let a = Abbrev_type.(make Var) in
      let pair = Abbrev_type.(make (Structure (Tuple [ a; a ]))) in
      Abbrev.(make (Constr ([ a ], "K")) pair)
    in
    let abbrev_f =
      let a = Abbrev_type.(make Var) in
      let arr = Abbrev_type.(make (Structure (Arrow (a, a)))) in
      Abbrev.(make (Constr ([ a ], "F")) arr)
    in
    let abbrev_g =
      let a = Abbrev_type.(make Var) in
      let k = Abbrev_type.(make (Structure (Constr ([ a ], "K")))) in
      let f = Abbrev_type.(make (Structure (Constr ([ k ], "F")))) in
      Abbrev.(make (Constr ([ a ], "G")) f)
    in
    Abbreviations.empty
    |> Abbreviations.add ~abbrev:abbrev_k
    |> Abbreviations.add ~abbrev:abbrev_f
    |> Abbreviations.add ~abbrev:abbrev_g
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
  print_infer_result ~abbrevs ~env:Env.empty exp;
  [%expect
    {|
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
                   └──Type expr: Constructor: G
                      └──Type expr: Constructor: int
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: G
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
                         └──Type expr: Constructor: G
                            └──Type expr: Constructor: int
                         └──Desc: Variable
                            └──Variable: f
                      └──Expression:
                         └──Type expr: Constructor: K
                            └──Type expr: Constructor: int
                         └──Desc: Variable
                            └──Variable: x |}]