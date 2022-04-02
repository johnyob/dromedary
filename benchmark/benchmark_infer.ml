open Core
open Core_bench
open Dromedary
open Parsing
open Typing
open Parsetree
open Ast_types
open Types
module Constraint = Typing.Private.Constraint
open Constraint

let t1 =
  Bench.Test.create
    ~name:"constant: int"
    (let exp = Pexp_const (Const_int 1) in
     fun () -> Typing.infer_exp ~env:Env.empty ~abbrevs:Abbreviations.empty exp)


let t2 =
  Bench.Test.create
    ~name:"primitives"
    (let exp =
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
     fun () -> Typing.infer_exp ~env:Env.empty ~abbrevs:Abbreviations.empty exp)


let t3 =
  Bench.Test.create
    ~name:"function - identity"
    (let exp = Pexp_fun (Ppat_var "x", Pexp_var "x") in
     fun () -> Typing.infer_exp ~env:Env.empty ~abbrevs:Abbreviations.empty exp)


let t4 =
  Bench.Test.create
    ~name:"function - curry"
    (let exp =
       Pexp_fun
         ( Ppat_var "f"
         , Pexp_fun
             ( Ppat_var "x"
             , Pexp_fun
                 ( Ppat_var "y"
                 , Pexp_app
                     (Pexp_var "f", Pexp_tuple [ Pexp_var "x"; Pexp_var "y" ])
                 ) ) )
     in
     fun () -> Typing.infer_exp ~env:Env.empty ~abbrevs:Abbreviations.empty exp)


let add_list env =
  let name = "list" in
  let a = Var.make () in
  let params = [ a ] in
  let a' = Types.of_var a in
  let type_ = make (Ttyp_constr ([ a' ], name)) in
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
                  ; constructor_arg_type = make (Ttyp_tuple [ a'; type_ ])
                  }
            ; constructor_type = type_
            ; constructor_constraints = []
            }
          ]
    }


let t5 =
  Bench.Test.create
    ~name:"function - hd"
    (let exp =
       Pexp_fun
         ( Ppat_construct
             ("Cons", Some ([], Ppat_tuple [ Ppat_var "x"; Ppat_any ]))
         , Pexp_var "x" )
     in
     let env = add_list Env.empty in
     fun () -> Typing.infer_exp ~env ~abbrevs:Abbreviations.empty exp)


let t6 =
  Bench.Test.create
    ~name:"let - map"
    (let exp =
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
                                             [ Ppat_var "x"; Ppat_var "xs" ] )
                                     )
                               ; pc_rhs =
                                   Pexp_construct
                                     ( "Cons"
                                     , Some
                                         (Pexp_tuple
                                            [ Pexp_app
                                                (Pexp_var "f", Pexp_var "x")
                                            ; Pexp_app
                                                ( Pexp_app
                                                    ( Pexp_var "map"
                                                    , Pexp_var "f" )
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
     let env = add_list Env.empty in
     fun () -> Typing.infer_exp ~env ~abbrevs:Abbreviations.empty exp)


let t7 =
  Bench.Test.create
    ~name:"let rec - polymorphic recursion"
    (let exp =
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
                       , Pexp_constraint (Pexp_var "x", Ptyp_constr ([], "int"))
                       ) )
             }
           ]
         , Pexp_var "id" )
     in
     fun () -> Typing.infer_exp ~env:Env.empty ~abbrevs:Abbreviations.empty exp)


let add_term env =
  let name = "term" in
  let a = Var.make () in
  let a' = Types.of_var a in
  let alphas = [ a ] in
  let type_ = make (Ttyp_constr ([ a' ], name)) in
  let int = make (Ttyp_constr ([], "int")) in
  let bool = make (Ttyp_constr ([], "bool")) in
  let b1 = Var.make () in
  let b2 = Var.make () in
  let b1' = Types.of_var b1 in
  let b2' = Types.of_var b2 in
  Env.add_type_decl
    env
    { type_name = name
    ; type_kind =
        Type_variant
          [ { constructor_name = "Int"
            ; constructor_alphas = alphas
            ; constructor_arg =
                Some { constructor_arg_betas = []; constructor_arg_type = int }
            ; constructor_type = type_
            ; constructor_constraints = [ a', int ]
            }
          ; { constructor_name = "Succ"
            ; constructor_alphas = alphas
            ; constructor_arg =
                Some
                  { constructor_arg_betas = []
                  ; constructor_arg_type = make (Ttyp_constr ([ int ], name))
                  }
            ; constructor_type = type_
            ; constructor_constraints = [ a', int ]
            }
          ; { constructor_name = "Bool"
            ; constructor_alphas = alphas
            ; constructor_arg =
                Some { constructor_arg_betas = []; constructor_arg_type = bool }
            ; constructor_type = type_
            ; constructor_constraints = [ a', bool ]
            }
          ; { constructor_name = "If"
            ; constructor_alphas = alphas
            ; constructor_arg =
                Some
                  { constructor_arg_betas = []
                  ; constructor_arg_type =
                      make
                        (Ttyp_tuple
                           [ make (Ttyp_constr ([ bool ], name))
                           ; make (Ttyp_constr ([ a' ], name))
                           ; make (Ttyp_constr ([ a' ], name))
                           ])
                  }
            ; constructor_type = type_
            ; constructor_constraints = []
            }
          ; { constructor_name = "Pair"
            ; constructor_alphas = alphas
            ; constructor_arg =
                Some
                  { constructor_arg_betas = [ b1; b2 ]
                  ; constructor_arg_type =
                      make
                        (Ttyp_tuple
                           [ make (Ttyp_constr ([ b1' ], name))
                           ; make (Ttyp_constr ([ b2' ], name))
                           ])
                  }
            ; constructor_type = type_
            ; constructor_constraints = [ a', make (Ttyp_tuple [ b1'; b2' ]) ]
            }
          ; { constructor_name = "Fst"
            ; constructor_alphas = alphas
            ; constructor_arg =
                Some
                  { constructor_arg_betas = [ b1; b2 ]
                  ; constructor_arg_type =
                      make
                        (Ttyp_constr ([ make (Ttyp_tuple [ b1'; b2' ]) ], name))
                  }
            ; constructor_type = type_
            ; constructor_constraints = [ a', b1' ]
            }
          ; { constructor_name = "Snd"
            ; constructor_alphas = alphas
            ; constructor_arg =
                Some
                  { constructor_arg_betas = [ b1; b2 ]
                  ; constructor_arg_type =
                      make
                        (Ttyp_constr ([ make (Ttyp_tuple [ b1'; b2' ]) ], name))
                  }
            ; constructor_type = type_
            ; constructor_constraints = [ a', b2' ]
            }
          ]
    }


let def_fst ~in_ =
  Pexp_let
    ( Nonrecursive
    , [ { pvb_forall_vars = []
        ; pvb_pat = Ppat_var "fst"
        ; pvb_expr =
            Pexp_fun (Ppat_tuple [ Ppat_var "x"; Ppat_any ], Pexp_var "x")
        }
      ]
    , in_ )


let def_snd ~in_ =
  Pexp_let
    ( Nonrecursive
    , [ { pvb_forall_vars = []
        ; pvb_pat = Ppat_var "snd"
        ; pvb_expr =
            Pexp_fun (Ppat_tuple [ Ppat_any; Ppat_var "x" ], Pexp_var "x")
        }
      ]
    , in_ )


let t8 =
  Bench.Test.create
    ~name:"gadt - eval"
    (let env = add_term Env.empty in
     let exp =
       def_fst
         ~in_:
           (def_snd
              ~in_:
                (Pexp_let
                   ( Recursive
                   , [ { pvb_forall_vars = [ "a" ]
                       ; pvb_pat = Ppat_var "eval"
                       ; pvb_expr =
                           Pexp_fun
                             ( Ppat_constraint
                                 ( Ppat_var "t"
                                 , Ptyp_constr ([ Ptyp_var "a" ], "term") )
                             , Pexp_constraint
                                 ( Pexp_match
                                     ( Pexp_var "t"
                                     , [ { pc_lhs =
                                             Ppat_construct
                                               ("Int", Some ([], Ppat_var "x"))
                                         ; pc_rhs = Pexp_var "x"
                                         }
                                       ; { pc_lhs =
                                             Ppat_construct
                                               ("Bool", Some ([], Ppat_var "x"))
                                         ; pc_rhs = Pexp_var "x"
                                         }
                                       ; { pc_lhs =
                                             Ppat_construct
                                               ("Succ", Some ([], Ppat_var "t"))
                                         ; pc_rhs =
                                             Pexp_app
                                               ( Pexp_app
                                                   ( Pexp_prim Prim_add
                                                   , Pexp_app
                                                       ( Pexp_var "eval"
                                                       , Pexp_var "t" ) )
                                               , Pexp_const (Const_int 1) )
                                         }
                                       ; { pc_lhs =
                                             Ppat_construct
                                               ( "If"
                                               , Some
                                                   ( []
                                                   , Ppat_tuple
                                                       [ Ppat_var "t1"
                                                       ; Ppat_var "t2"
                                                       ; Ppat_var "t3"
                                                       ] ) )
                                         ; pc_rhs =
                                             Pexp_ifthenelse
                                               ( Pexp_app
                                                   ( Pexp_var "eval"
                                                   , Pexp_var "t1" )
                                               , Pexp_app
                                                   ( Pexp_var "eval"
                                                   , Pexp_var "t2" )
                                               , Pexp_app
                                                   ( Pexp_var "eval"
                                                   , Pexp_var "t3" ) )
                                         }
                                       ; { pc_lhs =
                                             Ppat_construct
                                               ( "Pair"
                                               , Some
                                                   ( []
                                                   , Ppat_tuple
                                                       [ Ppat_var "t1"
                                                       ; Ppat_var "t2"
                                                       ] ) )
                                         ; pc_rhs =
                                             Pexp_tuple
                                               [ Pexp_app
                                                   ( Pexp_var "eval"
                                                   , Pexp_var "t1" )
                                               ; Pexp_app
                                                   ( Pexp_var "eval"
                                                   , Pexp_var "t2" )
                                               ]
                                         }
                                       ; { pc_lhs =
                                             Ppat_construct
                                               ("Fst", Some ([], Ppat_var "t"))
                                         ; pc_rhs =
                                             Pexp_app
                                               ( Pexp_var "fst"
                                               , Pexp_app
                                                   ( Pexp_var "eval"
                                                   , Pexp_var "t" ) )
                                         }
                                       ; { pc_lhs =
                                             Ppat_construct
                                               ("Snd", Some ([], Ppat_var "t"))
                                         ; pc_rhs =
                                             Pexp_app
                                               ( Pexp_var "snd"
                                               , Pexp_app
                                                   ( Pexp_var "eval"
                                                   , Pexp_var "t" ) )
                                         }
                                       ] )
                                 , Ptyp_var "a" ) )
                       }
                     ]
                   , Pexp_const Const_unit )))
     in
     fun () -> Typing.infer_exp ~env ~abbrevs:Abbreviations.empty exp)


let def_id ~in_ =
  Pexp_let
    ( Nonrecursive
    , [ { pvb_forall_vars = []
        ; pvb_pat = Ppat_var "id"
        ; pvb_expr = Pexp_fun (Ppat_var "x", Pexp_var "x")
        }
      ]
    , in_ )


let t9 =
  let rec loop n =
    match n with
    | 0 -> Pexp_var "id"
    | n -> Pexp_app (loop (n - 1), Pexp_var "id")
  in
  Bench.Test.create_indexed
    ~name:"id - stress test"
    ~args:[ 1; 5; 10; 50; 100; 200; 500; 1000; 2000 ]
    (fun n ->
      Staged.stage (fun () ->
          Typing.infer_exp
            ~env:Env.empty
            ~abbrevs:Abbreviations.empty
            (def_id ~in_:(loop n))))


let tests = [ t1; t2; t3; t4; t5; t6; t7; t8 ]
let command = Bench.make_command tests
let stress_command = Bench.make_command [ t9 ]