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

let add_list env =
  let name = "list" in
  let a = Type_var.make () in
  let params = [ a ] in
  let a' = Type_expr.make (Ttyp_var a) in
  let type_ = Type_expr.make (Ttyp_constr ([ a' ], name)) in
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
                  ; constructor_arg_type = Type_expr.make (Ttyp_tuple [ a'; type_ ])
                  }
            ; constructor_type = type_
            ; constructor_constraints = []
            }
          ]
    }


let add_term env =
  let name = "term" in
  let a = Type_var.make () in
  let a' = Type_expr.make (Ttyp_var a) in
  let alphas = [ a ] in
  let type_ = Type_expr.make (Ttyp_constr ([ a' ], name)) in
  let int = Type_expr.make (Ttyp_constr ([], "int")) in
  let bool = Type_expr.make (Ttyp_constr ([], "bool")) in
  let b1 = Type_var.make () in
  let b2 = Type_var.make () in
  let b1' = Type_expr.make (Ttyp_var b1) in
  let b2' = Type_expr.make (Ttyp_var b2) in
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
                  ; constructor_arg_type = Type_expr.make (Ttyp_constr ([ int ], name))
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
                      Type_expr.make
                        (Ttyp_tuple
                           [ Type_expr.make (Ttyp_constr ([ bool ], name))
                           ; Type_expr.make (Ttyp_constr ([ a' ], name))
                           ; Type_expr.make (Ttyp_constr ([ a' ], name))
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
                      Type_expr.make
                        (Ttyp_tuple
                           [ Type_expr.make (Ttyp_constr ([ b1' ], name))
                           ; Type_expr.make (Ttyp_constr ([ b2' ], name))
                           ])
                  }
            ; constructor_type = type_
            ; constructor_constraints = [ a', Type_expr.make (Ttyp_tuple [ b1'; b2' ]) ]
            }
          ; { constructor_name = "Fst"
            ; constructor_alphas = alphas
            ; constructor_arg =
                Some
                  { constructor_arg_betas = [ b1; b2 ]
                  ; constructor_arg_type =
                      Type_expr.make
                        (Ttyp_constr ([ Type_expr.make (Ttyp_tuple [ b1'; b2' ]) ], name))
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
                      Type_expr.make
                        (Ttyp_constr ([ Type_expr.make (Ttyp_tuple [ b1'; b2' ]) ], name))
                  }
            ; constructor_type = type_
            ; constructor_constraints = [ a', b2' ]
            }
          ]
    }


let create_test_infer_exp
    ~name
    ?(env = Env.empty)
    ?(abbrevs = Abbreviations.empty)
    exp
  =
  Bench.Test.create
    ~name
    (let exp =
       match Parsing.parse_expression_from_string exp with
       | Ok exp -> exp
       | Error _err -> raise_s [%sexp "Parsing error"]
     in
     fun () -> Typing.infer_exp ~env ~abbrevs exp)


let t1' =
  create_test_infer_exp
    ~name:"gcd"
    "let mod = fun (m : int) (n : int) -> 0 \n\
    \ in \n\
    \ let rec gcd = fun m n -> \n\
    \   if n = 0 then m else gcd n (mod m n)\n\
    \ in \n\
    \ gcd 55 200"


let t2' =
  create_test_infer_exp
    ~name:"fact"
    "let rec fact = fun n ->\n\
    \   if n = 0 then 1 else n * fact (n - 1)\n\
    \ in\n\
    \ fact 1000"


let t3' = create_test_infer_exp ~name:"arith" "1 + (2 / 1 - 0 * 1) = 12"

let t4' =
  create_test_infer_exp
    ~name:"making change"
    ~env:(add_list Env.empty)
    "let le = fun (m : int) (n : int) -> true in\n\
    \ let raise = fun () -> Nil in\n\
    \ let rec change = fun till amt -> \n\
    \   match (till, amt) with\n\
    \   ( (_, 0) -> Nil\n\
    \   | (Nil, _) -> raise ()\n\
    \   | (Cons (c, till), amt) ->\n\
    \       if le amt c then change till amt\n\
    \       else Cons (c, change (Cons (c, till)) (amt - c))\n\
    \   )\n\
    \ in ()"


let t5' =
  create_test_infer_exp
    ~name:"map"
    ~env:(add_list Env.empty)
    "let rec map = fun t f ->\n\
    \   match t with\n\
    \   ( Nil -> Nil\n\
    \   | Cons (x, t) -> Cons (f x, map t f)\n\
    \   )\n\
    \ in\n\
    \ let f = fun x -> x + 1 in\n\
    \ map Nil f"


let t6' =
  create_test_infer_exp
    ~name:"iter"
    ~env:(add_list Env.empty)
    "let rec iter = fun t f ->\n\
    \   match t with\n\
    \   ( Nil -> Nil\n\
    \   | Cons (x, t) -> f x; iter t f\n\
    \   )\n\
    \ in\n\
    \ iter Nil (fun _ -> ())"


let add_tree env =
  let name = "tree" in
  let a = Type_var.make () in
  let params = [ a ]
  and a' = Type_expr.make (Ttyp_var a) in
  let type_ = Type_expr.make (Ttyp_constr ([ a' ], name)) in
  Env.add_type_decl
    env
    { type_name = name
    ; type_kind =
        Type_variant
          [ { constructor_name = "Empty_tree"
            ; constructor_alphas = params
            ; constructor_arg = None
            ; constructor_type = type_
            ; constructor_constraints = []
            }
          ; { constructor_name = "Node"
            ; constructor_alphas = params
            ; constructor_arg =
                Some
                  { constructor_arg_betas = []
                  ; constructor_arg_type = Type_expr.make (Ttyp_tuple [ a'; type_; a' ])
                  }
            ; constructor_type = type_
            ; constructor_constraints = []
            }
          ]
    }


let add_option env =
  let name = "option" in
  let a = Type_var.make () in
  let params = [ a ]
  and a' = Type_expr.make (Ttyp_var a) in
  let type_ = Type_expr.make (Ttyp_constr ([ a' ], name)) in
  Env.add_type_decl
    env
    { type_name = name
    ; type_kind =
        Type_variant
          [ { constructor_name = "None"
            ; constructor_alphas = params
            ; constructor_arg = None
            ; constructor_type = type_
            ; constructor_constraints = []
            }
          ; { constructor_name = "Some"
            ; constructor_alphas = params
            ; constructor_arg =
                Some { constructor_arg_betas = []; constructor_arg_type = a' }
            ; constructor_type = type_
            ; constructor_constraints = []
            }
          ]
    }


let t7' =
  create_test_infer_exp
    ~name:"lookup (tree)"
    ~env:(Env.empty |> add_tree |> add_option)
    "let le = fun (m : int) (n : int) -> true\n\
    \ \n\
    \     in let rec lookup = fun t key ->\n\
    \  match t with\n\
    \  ( Empty_tree -> None\n\
    \  | Node (l, (key', x), r) -> \n\
    \      if key = key' then Some x else \n\
    \      if le key key' then lookup l key else\n\
    \      lookup r key\n\
    \  )\n\
    \ in ()"


let t8' =
  create_test_infer_exp
    ~name:"insertion sort"
    ~env:(Env.empty |> add_list)
    "let leq = fun (m : int) (n : int) -> true in\n\
    \ let rec insert = fun x t ->\n\
    \   match t with\n\
    \   ( Nil -> Cons (x, Nil)\n\
    \   | Cons (y, t) -> \n\
    \       if leq x y then Cons (x, Cons (y, t))\n\
    \       else Cons (y, insert x t)\n\
    \   )\n\
    \ in \n\
    \ let rec insertion_sort = fun t ->\n\
    \   match t with\n\
    \   ( Nil -> Nil\n\
    \   | Cons (x, t) -> insert x (insertion_sort t)\n\
    \   )\n\
    \ in\n\
    \ ()"


let t9' =
  create_test_infer_exp
    ~name:"is_even, is_odd"
    "let rec is_even = fun n -> \n\
    \   if n = 0 then true else is_odd (n - 1)\n\
    \ and is_odd = fun n -> \n\
    \   if n = 1 then true else is_even (n - 1)\n\
    \ in\n\
    \ ()"


let add_perfect_tree env =
  let name = "perfect_tree" in
  let a = Type_var.make () in
  let params = [ a ]
  and a' = Type_expr.make (Ttyp_var a) in
  let type_ = Type_expr.make (Ttyp_constr ([ a' ], name)) in
  Env.add_type_decl
    env
    { type_name = name
    ; type_kind =
        Type_variant
          [ { constructor_name = "Empty"
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
                      Type_expr.make
                        (Ttyp_tuple
                           [ a'
                           ; Type_expr.make
                               (Ttyp_constr
                                  ([ Type_expr.make (Ttyp_tuple [ a'; a' ]) ], name))
                           ])
                  }
            ; constructor_type = type_
            ; constructor_constraints = []
            }
          ]
    }


let t10' =
  create_test_infer_exp
    ~name:"perfect_tree length"
    ~env:(Env.empty |> add_perfect_tree)
    "let rec (type 'a) length = fun (t : 'a perfect_tree) -> \n\
    \   (\n\
    \     (match t with\n\
    \       ( Empty -> 0\n\
    \       | Cons (_, t) -> 1 + 2 * length t\n\
    \       )\n\
    \     ) : int\n\
    \   )\n\
    \ in ()"


let t11' =
  create_test_infer_exp
    ~name:"term eval"
    ~env:(Env.empty |> add_term)
    {|
      let fst = fun (x, y) -> x in
      let snd = fun (x, y) -> y in
      let rec (type 'a) eval = fun (t : 'a term) ->
        ((match t with 
            ( Int n -> n
            | Bool b -> b
            | Succ t -> (eval t) + 1
            | If (t1, t2, t3) -> if eval t1 then eval t2 else eval t3
            | Pair (t1, t2) -> (eval t1, eval t2)
            | Fst t -> fst (eval t)
            | Snd t -> snd (eval t)
            )) 
        : 'a)
      in ()
    |}


let add_key env =
  let a = Type_var.make () in
  let params = [ a ]
  and a' = Type_expr.make (Ttyp_var a) in
  let name = "key" in
  let type_ = Type_expr.make (Ttyp_constr ([ a' ], name)) in
  let int = Type_expr.make (Ttyp_constr ([], "int"))
  and string = Type_expr.make (Ttyp_constr ([], "string"))
  and bool = Type_expr.make (Ttyp_constr ([], "bool")) in
  Env.add_type_decl
    env
    { type_name = name
    ; type_kind =
        Type_variant
          [ { constructor_name = "String"
            ; constructor_alphas = params
            ; constructor_arg =
                Some { constructor_arg_betas = []; constructor_arg_type = int }
            ; constructor_type = type_
            ; constructor_constraints = [ a', string ]
            }
          ; { constructor_name = "Bool"
            ; constructor_alphas = params
            ; constructor_arg =
                Some { constructor_arg_betas = []; constructor_arg_type = int }
            ; constructor_type = type_
            ; constructor_constraints = [ a', bool ]
            }
          ]
    }


let add_elem env =
  let name = "elem" in
  let params = [] in
  let type_ = Type_expr.make (Ttyp_constr ([], name)) in
  let value = Type_var.make () in
  let value' = Type_expr.make (Ttyp_var value) in
  Env.add_type_decl
    env
    { type_name = name
    ; type_kind =
        Type_variant
          [ { constructor_name = "Elem"
            ; constructor_alphas = params
            ; constructor_arg =
                Some
                  { constructor_arg_betas = [ value ]
                  ; constructor_arg_type =
                      Type_expr.make
                        (Ttyp_tuple
                           [ Type_expr.make (Ttyp_constr ([ value' ], "key")); value' ])
                  }
            ; constructor_type = type_
            ; constructor_constraints = []
            }
          ]
    }


let add_dependent_assoc_list abbrevs =
  let open Typing.Private.Algebra.Type_former in
  let name = "dep_assoc_list" in
  let elem = Abbrev_type.make_former (Constr ([], "elem")) in
  Abbreviations.add
    abbrevs
    ~abbrev:
      (Constr ([], name), Abbrev_type.make_former (Constr ([ elem ], "list")))


let add_elem_mapper env =
  let name = "elem_mapper" in
  let a = Type_var.make () in
  let a' = Type_expr.make (Ttyp_var a) in
  let type_ = Type_expr.make (Ttyp_constr ([], name)) in
  Env.add_type_decl
    env
    { type_name = name
    ; type_kind =
        Type_record
          [ { label_name = "f"
            ; label_alphas = []
            ; label_betas = [ a ]
            ; label_arg =
                Type_expr.make
                  (Ttyp_arrow
                     ( Type_expr.make (Ttyp_constr ([ a' ], "key"))
                     , Type_expr.make (Ttyp_arrow (a', a')) ))
            ; label_type = type_
            }
          ]
    }


let t12' =
  create_test_infer_exp
    ~name:"dependent associative list map_elem"
    ~env:(Env.empty |> add_key |> add_elem |> add_list |> add_elem_mapper)
    {|
      let rec map = fun t f ->
        match t with
        ( Nil -> Nil
        | Cons (x, t) -> Cons (f x, map t f)
        )
      in
      let map_elem = fun (Elem (key, value)) mapper ->
        Elem (key, mapper.f key value)
      in
      let map_assoc_list = fun t mapper ->
        map t (fun elem -> map_elem elem mapper)
      in () 
    |}


let tests = [ t1'; t2'; t3'; t4'; t5'; t6'; t7'; t8'; t9'; t10'; t11'; t12' ]
let command = Bench.make_command tests

let def_id ~in_ =
  Pexp_let
    ( Nonrecursive
    , [ { pvb_forall_vars = []
        ; pvb_pat = Ppat_var "id"
        ; pvb_expr = Pexp_fun (Ppat_var "x", Pexp_var "x")
        }
      ]
    , in_ )


let id_app_stress_test =
  let rec loop n =
    match n with
    | 0 -> Pexp_var "id"
    | n -> Pexp_app (loop (n - 1), Pexp_var "id")
  in
  Bench.Test.create_indexed
    ~name:"id app - stress test"
    ~args:[ 1; 5; 10; 50; 100; 200; 500; 1000; 2000 ]
    (fun n ->
      Staged.stage (fun () ->
          Typing.infer_exp
            ~env:Env.empty
            ~abbrevs:Abbreviations.empty
            (def_id ~in_:(loop n))))


let def_pair ~in_ =
  Pexp_let
    ( Nonrecursive
    , [ { pvb_forall_vars = []
        ; pvb_pat = Ppat_var "pair"
        ; pvb_expr =
            Pexp_fun
              ( Ppat_var "x"
              , Pexp_fun
                  ( Ppat_var "f"
                  , Pexp_app
                      (Pexp_app (Pexp_var "f", Pexp_var "x"), Pexp_var "x") ) )
        }
      ]
    , in_ )


let id_let_stress_test = 
  let rec loop n = 
    match n with
    | 0 -> Pexp_const Const_unit
    | n -> def_id ~in_:(loop (n - 1))
  in
  Bench.Test.create_indexed
    ~name:"id let - stress test"
    ~args:[ 1; 5; 10; 50; 100; 200; 500; 1000; 2000 ]
    (fun n ->
      Staged.stage (fun () ->
          Typing.infer_exp
            ~env:Env.empty
            ~abbrevs:Abbreviations.empty
            (loop n)))
let pair_let_stress_test =
  let def_f0 ~in_ =
    Pexp_let
      ( Nonrecursive
      , [ { pvb_forall_vars = []
          ; pvb_pat = Ppat_var "f0"
          ; pvb_expr =
              Pexp_fun (Ppat_var "x", Pexp_app (Pexp_var "pair", Pexp_var "x"))
          }
        ]
      , in_ )
  in
  let rec loop i n =
    if i = n
    then
      (* fun z -> fn (fun x -> x) z *)
      Pexp_fun
        ( Ppat_var "z"
        , Pexp_app
            ( Pexp_app
                ( Pexp_var ("f" ^ Int.to_string n)
                , Pexp_fun (Ppat_var "x", Pexp_var "x") )
            , Pexp_var "z" ) )
    else (
      assert (i >= 1);
      Pexp_let
        ( Nonrecursive
        , [ { pvb_forall_vars = []
            ; pvb_pat = Ppat_var ("f" ^ Int.to_string i)
            ; pvb_expr =
                (let f = "f" ^ Int.to_string (i - 1) in
                 Pexp_fun
                   ( Ppat_var "x"
                   , Pexp_app (Pexp_var f, Pexp_app (Pexp_var f, Pexp_var "x"))
                   ))
            }
          ]
        , loop (i + 1) n ))
  in
  Bench.Test.create_indexed
    ~name:"pair let - stress test"
    ~args:[ 1;2;3;4;5;6 ]
    (fun n ->
      Staged.stage (fun () ->
          let exp = def_pair ~in_:(def_f0 ~in_:(loop 1 n)) in
          Typing.infer_exp ~env:Env.empty ~abbrevs:Abbreviations.empty exp))


let stress_tests = [ pair_let_stress_test ]
let stress_command = Bench.make_command stress_tests