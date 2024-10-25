open! Import
open Util

let%expect_test "" =
  let str =
    {|
      (* Prelude / Stdlib *)
      type 'a list =
        | Nil
        | Cons of 'a * 'a list
      ;;
      
      external fold_left : 'a 'b. ('b -> 'a -> 'b) -> 'b -> 'a list -> 'b = "%fold_left";;
      external fold_right : 'a 'b. ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b = "%fold_right";;

      external eq : 'a. 'a -> 'a -> bool = "%equal";;
      external lt : 'a. 'a -> 'a -> bool = "%less_than";;
      external leq : 'a. 'a -> 'a -> bool = "%less_than_equal";;

      type 'a option = 
        | None
        | Some of 'a
      ;;

      (* Lambda calculus - Term structure *)

      type var = 
        | Free of string
        | Bound of int
      ;;

      type expr = 
        | Var of var
        | Fun of string * expr
        | App of expr * expr
      ;;

      let bind_var = fun i x var ->
        match var with
        ( Free y -> if eq x y then Bound i else Free y
        | Bound j -> Bound j
        )
      ;;

      let rec bind = fun i x exp ->
        match exp with
        ( Var var -> Var (bind_var i x var)
        | Fun (y, exp) -> Fun (y, bind (i + 1) x exp)
        | App (exp1, exp2) -> App (bind i x exp1, bind i x exp2)
        )
      ;;

      let binds = fun xs exp ->
        fold_right (fun x exp -> Fun (x, bind 0 x exp)) exp xs
      ;;

      let app = fun exp exps ->
        fold_left (fun exp1 exp2 -> App (exp1, exp2)) exp exps
      ;;

      let shift = fun i exp ->
        let rec loop = fun depth exp ->
          match exp with
          ( Var (Free x)  -> Var (Free x)
          | Var (Bound j) -> Var (if leq depth j then Bound (j + i) else Bound j)
          | Fun (x, exp) -> Fun (x, loop (depth + 1) exp)
          | App (exp1, exp2) -> App (loop depth exp1, loop depth exp2)
          )
        in loop 0 exp
      ;;

      let rec subst = fun i iexp exp ->
        match exp with
        ( Var (Free x) -> Var (Free x)
        | Var (Bound j) ->
          if lt j i then Var (Bound j)
          else if eq j i then shift i iexp
          else (* lt i j *) Var (Bound (j - 1))
        | Fun (x, exp) -> Fun (x, subst (i + 1) iexp exp)
        | App (exp1, exp2) -> App (subst i iexp exp1, subst i exp exp2)  
        )
      ;;

      external lookup : (string * expr) list -> string -> expr option = "%lookup";;

      let rec inst = fun env exp ->
        match exp with
        ( Var (Free x) -> 
          match lookup env x with
          ( Some exp -> exp
          | None -> Var (Free x)
          )
        | Var (Bound i) -> Var (Bound i)
        | Fun (x, exp) -> Fun (x, inst env exp)
        | App (exp1, exp2) -> App (inst env exp1, inst env exp2)
        )
      ;;

      (* Reduce / Eval *)

      let rec eval = fun exp ->
        match exp with
        ( App (exp1, exp2) ->
          match eval exp1 with
          ( Fun (x, exp) -> eval (subst 0 (eval exp2) exp)
          | exp1 -> App (exp1, eval exp2)
          )
        | exp -> exp 
        )
      ;;

      let rec by_value = fun exp ->
         bodies (eval exp)
      and bodies = fun exp ->
         match exp with
         ( Fun (x, exp) -> Fun (x, by_value exp)
         | App (exp1, exp2) -> App (bodies exp1, exp2)
         | exp -> exp
         )
      ;;

      let rec head_nf = fun exp ->
         match exp with
         ( Fun (x, exp) -> Fun (x, head_nf exp)
         | App (exp1, exp2) ->
            match head_nf exp1 with
            ( Fun (x, exp) -> head_nf (subst 0 exp2 exp)
            | exp1 -> App (exp1, exp2)
            )
         | exp -> exp
         )
      ;;

      let rec by_name = fun exp ->
         args (head_nf exp)
      and args = fun exp ->
         match exp with
         ( Fun (x, exp) -> Fun (x, args exp)
         | App (exp1, exp2) -> App (args exp1, by_name exp2)
         | exp -> exp
         )
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: 89
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 89
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 89
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 89
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: 89
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 89
       └──Structure item: Primitive
          └──Value description:
             └──Name: fold_left
             └──Scheme:
                └──Variables: 0,1
                └──Type expr: Arrow
                   └──Type expr: Arrow
                      └──Type expr: Variable: 1
                      └──Type expr: Arrow
                         └──Type expr: Variable: 0
                         └──Type expr: Variable: 1
                   └──Type expr: Arrow
                      └──Type expr: Variable: 1
                      └──Type expr: Arrow
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 0
                         └──Type expr: Variable: 1
             └──Primitive name: %fold_left
       └──Structure item: Primitive
          └──Value description:
             └──Name: fold_right
             └──Scheme:
                └──Variables: 15,14
                └──Type expr: Arrow
                   └──Type expr: Arrow
                      └──Type expr: Variable: 14
                      └──Type expr: Arrow
                         └──Type expr: Variable: 15
                         └──Type expr: Variable: 15
                   └──Type expr: Arrow
                      └──Type expr: Variable: 15
                      └──Type expr: Arrow
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 14
                         └──Type expr: Variable: 15
             └──Primitive name: %fold_right
       └──Structure item: Primitive
          └──Value description:
             └──Name: eq
             └──Scheme:
                └──Variables: 28
                └──Type expr: Arrow
                   └──Type expr: Variable: 28
                   └──Type expr: Arrow
                      └──Type expr: Variable: 28
                      └──Type expr: Constructor: bool
             └──Primitive name: %equal
       └──Structure item: Primitive
          └──Value description:
             └──Name: lt
             └──Scheme:
                └──Variables: 35
                └──Type expr: Arrow
                   └──Type expr: Variable: 35
                   └──Type expr: Arrow
                      └──Type expr: Variable: 35
                      └──Type expr: Constructor: bool
             └──Primitive name: %less_than
       └──Structure item: Primitive
          └──Value description:
             └──Name: leq
             └──Scheme:
                └──Variables: 42
                └──Type expr: Arrow
                   └──Type expr: Variable: 42
                   └──Type expr: Arrow
                      └──Type expr: Variable: 42
                      └──Type expr: Constructor: bool
             └──Primitive name: %less_than_equal
       └──Structure item: Type
          └──Type declaration:
             └──Type name: option
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: None
                   └──Constructor alphas: 94
                   └──Constructor type:
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: 94
                └──Constructor declaration:
                   └──Constructor name: Some
                   └──Constructor alphas: 94
                   └──Constructor type:
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: 94
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: 94
       └──Structure item: Type
          └──Type declaration:
             └──Type name: var
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Free
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: var
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: string
                └──Constructor declaration:
                   └──Constructor name: Bound
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: var
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: int
       └──Structure item: Type
          └──Type declaration:
             └──Type name: expr
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Var
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: expr
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: var
                └──Constructor declaration:
                   └──Constructor name: Fun
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: expr
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Constructor: string
                         └──Type expr: Constructor: expr
                └──Constructor declaration:
                   └──Constructor name: App
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: expr
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Constructor: expr
                         └──Type expr: Constructor: expr
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: int
                      └──Type expr: Arrow
                         └──Type expr: Constructor: string
                         └──Type expr: Arrow
                            └──Type expr: Constructor: var
                            └──Type expr: Constructor: var
                   └──Desc: Variable: bind_var
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Constructor: string
                            └──Type expr: Arrow
                               └──Type expr: Constructor: var
                               └──Type expr: Constructor: var
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: i
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: string
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: var
                                  └──Type expr: Constructor: var
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: string
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: var
                                     └──Type expr: Constructor: var
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: var
                                        └──Desc: Variable: var
                                     └──Expression:
                                        └──Type expr: Constructor: var
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: var
                                              └──Desc: Variable
                                                 └──Variable: var
                                           └──Type expr: Constructor: var
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: var
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Free
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: string
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: var
                                                       └──Pattern:
                                                          └──Type expr: Constructor: string
                                                          └──Desc: Variable: y
                                                 └──Expression:
                                                    └──Type expr: Constructor: var
                                                    └──Desc: If
                                                       └──Expression:
                                                          └──Type expr: Constructor: bool
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: string
                                                                   └──Type expr: Constructor: bool
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: string
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: string
                                                                            └──Type expr: Constructor: bool
                                                                      └──Desc: Variable
                                                                         └──Variable: eq
                                                                         └──Type expr: Constructor: string
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: string
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: string
                                                                └──Desc: Variable
                                                                   └──Variable: y
                                                       └──Expression:
                                                          └──Type expr: Constructor: var
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Bound
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: int
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: var
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: i
                                                       └──Expression:
                                                          └──Type expr: Constructor: var
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Free
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: string
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: var
                                                             └──Expression:
                                                                └──Type expr: Constructor: string
                                                                └──Desc: Variable
                                                                   └──Variable: y
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: var
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Bound
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: var
                                                       └──Pattern:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable: j
                                                 └──Expression:
                                                    └──Type expr: Constructor: var
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Bound
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: var
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: j
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: bind
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Constructor: string
                            └──Type expr: Arrow
                               └──Type expr: Constructor: expr
                               └──Type expr: Constructor: expr
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: i
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: string
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: expr
                                  └──Type expr: Constructor: expr
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: string
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: expr
                                     └──Type expr: Constructor: expr
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Variable: exp
                                     └──Expression:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: expr
                                              └──Desc: Variable
                                                 └──Variable: exp
                                           └──Type expr: Constructor: expr
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Var
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: var
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: expr
                                                       └──Pattern:
                                                          └──Type expr: Constructor: var
                                                          └──Desc: Variable: var
                                                 └──Expression:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Var
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: var
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: expr
                                                       └──Expression:
                                                          └──Type expr: Constructor: var
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: var
                                                                   └──Type expr: Constructor: var
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: string
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: var
                                                                            └──Type expr: Constructor: var
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: int
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: string
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: var
                                                                                     └──Type expr: Constructor: var
                                                                            └──Desc: Variable
                                                                               └──Variable: bind_var
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: int
                                                                            └──Desc: Variable
                                                                               └──Variable: i
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: string
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: var
                                                                └──Desc: Variable
                                                                   └──Variable: var
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fun
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: string
                                                                └──Type expr: Constructor: expr
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: expr
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: string
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: string
                                                                └──Desc: Variable: y
                                                             └──Pattern:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Variable: exp
                                                 └──Expression:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fun
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: string
                                                                └──Type expr: Constructor: expr
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: expr
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: string
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Constructor: string
                                                                └──Desc: Variable
                                                                   └──Variable: y
                                                             └──Expression:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: expr
                                                                         └──Type expr: Constructor: expr
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: string
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: expr
                                                                                  └──Type expr: Constructor: expr
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: int
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: string
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Constructor: expr
                                                                                           └──Type expr: Constructor: expr
                                                                                  └──Desc: Variable
                                                                                     └──Variable: bind
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
                                                                                                 └──Variable: i
                                                                                     └──Expression:
                                                                                        └──Type expr: Constructor: int
                                                                                        └──Desc: Constant: 1
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: string
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: expr
                                                                      └──Desc: Variable
                                                                         └──Variable: exp
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: App
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: expr
                                                                └──Type expr: Constructor: expr
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: expr
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: expr
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Variable: exp1
                                                             └──Pattern:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Variable: exp2
                                                 └──Expression:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: App
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: expr
                                                                └──Type expr: Constructor: expr
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: expr
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: expr
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: expr
                                                                         └──Type expr: Constructor: expr
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: string
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: expr
                                                                                  └──Type expr: Constructor: expr
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: int
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: string
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Constructor: expr
                                                                                           └──Type expr: Constructor: expr
                                                                                  └──Desc: Variable
                                                                                     └──Variable: bind
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: int
                                                                                  └──Desc: Variable
                                                                                     └──Variable: i
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: string
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: expr
                                                                      └──Desc: Variable
                                                                         └──Variable: exp1
                                                             └──Expression:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: expr
                                                                         └──Type expr: Constructor: expr
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: string
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: expr
                                                                                  └──Type expr: Constructor: expr
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: int
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: string
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Constructor: expr
                                                                                           └──Type expr: Constructor: expr
                                                                                  └──Desc: Variable
                                                                                     └──Variable: bind
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: int
                                                                                  └──Desc: Variable
                                                                                     └──Variable: i
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: string
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: expr
                                                                      └──Desc: Variable
                                                                         └──Variable: exp2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: list
                         └──Type expr: Constructor: string
                      └──Type expr: Arrow
                         └──Type expr: Constructor: expr
                         └──Type expr: Constructor: expr
                   └──Desc: Variable: binds
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: list
                            └──Type expr: Constructor: string
                         └──Type expr: Arrow
                            └──Type expr: Constructor: expr
                            └──Type expr: Constructor: expr
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: string
                            └──Desc: Variable: xs
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: expr
                               └──Type expr: Constructor: expr
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: expr
                                  └──Desc: Variable: exp
                               └──Expression:
                                  └──Type expr: Constructor: expr
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: list
                                              └──Type expr: Constructor: string
                                           └──Type expr: Constructor: expr
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: expr
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: string
                                                    └──Type expr: Constructor: expr
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: string
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: expr
                                                             └──Type expr: Constructor: expr
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: expr
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: string
                                                             └──Type expr: Constructor: expr
                                                    └──Desc: Variable
                                                       └──Variable: fold_right
                                                       └──Type expr: Constructor: expr
                                                       └──Type expr: Constructor: string
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: string
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: expr
                                                          └──Type expr: Constructor: expr
                                                    └──Desc: Function
                                                       └──Pattern:
                                                          └──Type expr: Constructor: string
                                                          └──Desc: Variable: x
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: expr
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Function
                                                             └──Pattern:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Variable: exp
                                                             └──Expression:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Fun
                                                                      └──Constructor argument type:
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Constructor: string
                                                                            └──Type expr: Constructor: expr
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: expr
                                                                   └──Expression:
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Constructor: string
                                                                         └──Type expr: Constructor: expr
                                                                      └──Desc: Tuple
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: string
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: expr
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: expr
                                                                                     └──Type expr: Constructor: expr
                                                                                  └──Desc: Application
                                                                                     └──Expression:
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Constructor: string
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Constructor: expr
                                                                                              └──Type expr: Constructor: expr
                                                                                        └──Desc: Application
                                                                                           └──Expression:
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Constructor: int
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Constructor: string
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Constructor: expr
                                                                                                       └──Type expr: Constructor: expr
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: bind
                                                                                           └──Expression:
                                                                                              └──Type expr: Constructor: int
                                                                                              └──Desc: Constant: 0
                                                                                     └──Expression:
                                                                                        └──Type expr: Constructor: string
                                                                                        └──Desc: Variable
                                                                                           └──Variable: x
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: expr
                                                                                  └──Desc: Variable
                                                                                     └──Variable: exp
                                           └──Expression:
                                              └──Type expr: Constructor: expr
                                              └──Desc: Variable
                                                 └──Variable: exp
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Constructor: string
                                        └──Desc: Variable
                                           └──Variable: xs
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: expr
                      └──Type expr: Arrow
                         └──Type expr: Constructor: list
                            └──Type expr: Constructor: expr
                         └──Type expr: Constructor: expr
                   └──Desc: Variable: app
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: expr
                         └──Type expr: Arrow
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: expr
                            └──Type expr: Constructor: expr
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: expr
                            └──Desc: Variable: exp
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: list
                                  └──Type expr: Constructor: expr
                               └──Type expr: Constructor: expr
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Constructor: expr
                                  └──Desc: Variable: exps
                               └──Expression:
                                  └──Type expr: Constructor: expr
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: list
                                              └──Type expr: Constructor: expr
                                           └──Type expr: Constructor: expr
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: expr
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: expr
                                                    └──Type expr: Constructor: expr
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: expr
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: expr
                                                             └──Type expr: Constructor: expr
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: expr
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: expr
                                                             └──Type expr: Constructor: expr
                                                    └──Desc: Variable
                                                       └──Variable: fold_left
                                                       └──Type expr: Constructor: expr
                                                       └──Type expr: Constructor: expr
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: expr
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: expr
                                                          └──Type expr: Constructor: expr
                                                    └──Desc: Function
                                                       └──Pattern:
                                                          └──Type expr: Constructor: expr
                                                          └──Desc: Variable: exp1
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: expr
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Function
                                                             └──Pattern:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Variable: exp2
                                                             └──Expression:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: App
                                                                      └──Constructor argument type:
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Constructor: expr
                                                                            └──Type expr: Constructor: expr
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: expr
                                                                   └──Expression:
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Constructor: expr
                                                                         └──Type expr: Constructor: expr
                                                                      └──Desc: Tuple
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: expr
                                                                            └──Desc: Variable
                                                                               └──Variable: exp1
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: expr
                                                                            └──Desc: Variable
                                                                               └──Variable: exp2
                                           └──Expression:
                                              └──Type expr: Constructor: expr
                                              └──Desc: Variable
                                                 └──Variable: exp
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Constructor: expr
                                        └──Desc: Variable
                                           └──Variable: exps
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: int
                      └──Type expr: Arrow
                         └──Type expr: Constructor: expr
                         └──Type expr: Constructor: expr
                   └──Desc: Variable: shift
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Constructor: expr
                            └──Type expr: Constructor: expr
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: i
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: expr
                               └──Type expr: Constructor: expr
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: expr
                                  └──Desc: Variable: exp
                               └──Expression:
                                  └──Type expr: Constructor: expr
                                  └──Desc: Let rec
                                     └──Value bindings:
                                        └──Value binding:
                                           └──Variable: loop
                                           └──Abstraction:
                                              └──Variables:
                                              └──Expression:
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: expr
                                                       └──Type expr: Constructor: expr
                                                 └──Desc: Function
                                                    └──Pattern:
                                                       └──Type expr: Constructor: int
                                                       └──Desc: Variable: depth
                                                    └──Expression:
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: expr
                                                          └──Type expr: Constructor: expr
                                                       └──Desc: Function
                                                          └──Pattern:
                                                             └──Type expr: Constructor: expr
                                                             └──Desc: Variable: exp
                                                          └──Expression:
                                                             └──Type expr: Constructor: expr
                                                             └──Desc: Match
                                                                └──Expression:
                                                                   └──Type expr: Constructor: expr
                                                                   └──Desc: Variable
                                                                      └──Variable: exp
                                                                └──Type expr: Constructor: expr
                                                                └──Cases:
                                                                   └──Case:
                                                                      └──Pattern:
                                                                         └──Type expr: Constructor: expr
                                                                         └──Desc: Construct
                                                                            └──Constructor description:
                                                                               └──Name: Var
                                                                               └──Constructor argument type:
                                                                                  └──Type expr: Constructor: var
                                                                               └──Constructor type:
                                                                                  └──Type expr: Constructor: expr
                                                                            └──Pattern:
                                                                               └──Type expr: Constructor: var
                                                                               └──Desc: Construct
                                                                                  └──Constructor description:
                                                                                     └──Name: Free
                                                                                     └──Constructor argument type:
                                                                                        └──Type expr: Constructor: string
                                                                                     └──Constructor type:
                                                                                        └──Type expr: Constructor: var
                                                                                  └──Pattern:
                                                                                     └──Type expr: Constructor: string
                                                                                     └──Desc: Variable: x
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: expr
                                                                         └──Desc: Construct
                                                                            └──Constructor description:
                                                                               └──Name: Var
                                                                               └──Constructor argument type:
                                                                                  └──Type expr: Constructor: var
                                                                               └──Constructor type:
                                                                                  └──Type expr: Constructor: expr
                                                                            └──Expression:
                                                                               └──Type expr: Constructor: var
                                                                               └──Desc: Construct
                                                                                  └──Constructor description:
                                                                                     └──Name: Free
                                                                                     └──Constructor argument type:
                                                                                        └──Type expr: Constructor: string
                                                                                     └──Constructor type:
                                                                                        └──Type expr: Constructor: var
                                                                                  └──Expression:
                                                                                     └──Type expr: Constructor: string
                                                                                     └──Desc: Variable
                                                                                        └──Variable: x
                                                                   └──Case:
                                                                      └──Pattern:
                                                                         └──Type expr: Constructor: expr
                                                                         └──Desc: Construct
                                                                            └──Constructor description:
                                                                               └──Name: Var
                                                                               └──Constructor argument type:
                                                                                  └──Type expr: Constructor: var
                                                                               └──Constructor type:
                                                                                  └──Type expr: Constructor: expr
                                                                            └──Pattern:
                                                                               └──Type expr: Constructor: var
                                                                               └──Desc: Construct
                                                                                  └──Constructor description:
                                                                                     └──Name: Bound
                                                                                     └──Constructor argument type:
                                                                                        └──Type expr: Constructor: int
                                                                                     └──Constructor type:
                                                                                        └──Type expr: Constructor: var
                                                                                  └──Pattern:
                                                                                     └──Type expr: Constructor: int
                                                                                     └──Desc: Variable: j
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: expr
                                                                         └──Desc: Construct
                                                                            └──Constructor description:
                                                                               └──Name: Var
                                                                               └──Constructor argument type:
                                                                                  └──Type expr: Constructor: var
                                                                               └──Constructor type:
                                                                                  └──Type expr: Constructor: expr
                                                                            └──Expression:
                                                                               └──Type expr: Constructor: var
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
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: leq
                                                                                                    └──Type expr: Constructor: int
                                                                                              └──Expression:
                                                                                                 └──Type expr: Constructor: int
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: depth
                                                                                        └──Expression:
                                                                                           └──Type expr: Constructor: int
                                                                                           └──Desc: Variable
                                                                                              └──Variable: j
                                                                                  └──Expression:
                                                                                     └──Type expr: Constructor: var
                                                                                     └──Desc: Construct
                                                                                        └──Constructor description:
                                                                                           └──Name: Bound
                                                                                           └──Constructor argument type:
                                                                                              └──Type expr: Constructor: int
                                                                                           └──Constructor type:
                                                                                              └──Type expr: Constructor: var
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
                                                                                                          └──Variable: j
                                                                                              └──Expression:
                                                                                                 └──Type expr: Constructor: int
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: i
                                                                                  └──Expression:
                                                                                     └──Type expr: Constructor: var
                                                                                     └──Desc: Construct
                                                                                        └──Constructor description:
                                                                                           └──Name: Bound
                                                                                           └──Constructor argument type:
                                                                                              └──Type expr: Constructor: int
                                                                                           └──Constructor type:
                                                                                              └──Type expr: Constructor: var
                                                                                        └──Expression:
                                                                                           └──Type expr: Constructor: int
                                                                                           └──Desc: Variable
                                                                                              └──Variable: j
                                                                   └──Case:
                                                                      └──Pattern:
                                                                         └──Type expr: Constructor: expr
                                                                         └──Desc: Construct
                                                                            └──Constructor description:
                                                                               └──Name: Fun
                                                                               └──Constructor argument type:
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Constructor: string
                                                                                     └──Type expr: Constructor: expr
                                                                               └──Constructor type:
                                                                                  └──Type expr: Constructor: expr
                                                                            └──Pattern:
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Constructor: string
                                                                                  └──Type expr: Constructor: expr
                                                                               └──Desc: Tuple
                                                                                  └──Pattern:
                                                                                     └──Type expr: Constructor: string
                                                                                     └──Desc: Variable: x
                                                                                  └──Pattern:
                                                                                     └──Type expr: Constructor: expr
                                                                                     └──Desc: Variable: exp
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: expr
                                                                         └──Desc: Construct
                                                                            └──Constructor description:
                                                                               └──Name: Fun
                                                                               └──Constructor argument type:
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Constructor: string
                                                                                     └──Type expr: Constructor: expr
                                                                               └──Constructor type:
                                                                                  └──Type expr: Constructor: expr
                                                                            └──Expression:
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Constructor: string
                                                                                  └──Type expr: Constructor: expr
                                                                               └──Desc: Tuple
                                                                                  └──Expression:
                                                                                     └──Type expr: Constructor: string
                                                                                     └──Desc: Variable
                                                                                        └──Variable: x
                                                                                  └──Expression:
                                                                                     └──Type expr: Constructor: expr
                                                                                     └──Desc: Application
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Constructor: expr
                                                                                              └──Type expr: Constructor: expr
                                                                                           └──Desc: Application
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Constructor: int
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Constructor: expr
                                                                                                       └──Type expr: Constructor: expr
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: loop
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
                                                                                                                └──Variable: depth
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Constructor: int
                                                                                                       └──Desc: Constant: 1
                                                                                        └──Expression:
                                                                                           └──Type expr: Constructor: expr
                                                                                           └──Desc: Variable
                                                                                              └──Variable: exp
                                                                   └──Case:
                                                                      └──Pattern:
                                                                         └──Type expr: Constructor: expr
                                                                         └──Desc: Construct
                                                                            └──Constructor description:
                                                                               └──Name: App
                                                                               └──Constructor argument type:
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Constructor: expr
                                                                                     └──Type expr: Constructor: expr
                                                                               └──Constructor type:
                                                                                  └──Type expr: Constructor: expr
                                                                            └──Pattern:
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Constructor: expr
                                                                                  └──Type expr: Constructor: expr
                                                                               └──Desc: Tuple
                                                                                  └──Pattern:
                                                                                     └──Type expr: Constructor: expr
                                                                                     └──Desc: Variable: exp1
                                                                                  └──Pattern:
                                                                                     └──Type expr: Constructor: expr
                                                                                     └──Desc: Variable: exp2
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: expr
                                                                         └──Desc: Construct
                                                                            └──Constructor description:
                                                                               └──Name: App
                                                                               └──Constructor argument type:
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Constructor: expr
                                                                                     └──Type expr: Constructor: expr
                                                                               └──Constructor type:
                                                                                  └──Type expr: Constructor: expr
                                                                            └──Expression:
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Constructor: expr
                                                                                  └──Type expr: Constructor: expr
                                                                               └──Desc: Tuple
                                                                                  └──Expression:
                                                                                     └──Type expr: Constructor: expr
                                                                                     └──Desc: Application
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Constructor: expr
                                                                                              └──Type expr: Constructor: expr
                                                                                           └──Desc: Application
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Constructor: int
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Constructor: expr
                                                                                                       └──Type expr: Constructor: expr
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: loop
                                                                                              └──Expression:
                                                                                                 └──Type expr: Constructor: int
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: depth
                                                                                        └──Expression:
                                                                                           └──Type expr: Constructor: expr
                                                                                           └──Desc: Variable
                                                                                              └──Variable: exp1
                                                                                  └──Expression:
                                                                                     └──Type expr: Constructor: expr
                                                                                     └──Desc: Application
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Constructor: expr
                                                                                              └──Type expr: Constructor: expr
                                                                                           └──Desc: Application
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Constructor: int
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Constructor: expr
                                                                                                       └──Type expr: Constructor: expr
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: loop
                                                                                              └──Expression:
                                                                                                 └──Type expr: Constructor: int
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: depth
                                                                                        └──Expression:
                                                                                           └──Type expr: Constructor: expr
                                                                                           └──Desc: Variable
                                                                                              └──Variable: exp2
                                     └──Expression:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: expr
                                                 └──Type expr: Constructor: expr
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: expr
                                                          └──Type expr: Constructor: expr
                                                    └──Desc: Variable
                                                       └──Variable: loop
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 0
                                           └──Expression:
                                              └──Type expr: Constructor: expr
                                              └──Desc: Variable
                                                 └──Variable: exp
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: subst
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Constructor: expr
                            └──Type expr: Arrow
                               └──Type expr: Constructor: expr
                               └──Type expr: Constructor: expr
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: i
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: expr
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: expr
                                  └──Type expr: Constructor: expr
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: expr
                                  └──Desc: Variable: iexp
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: expr
                                     └──Type expr: Constructor: expr
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Variable: exp
                                     └──Expression:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: expr
                                              └──Desc: Variable
                                                 └──Variable: exp
                                           └──Type expr: Constructor: expr
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Var
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: var
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: expr
                                                       └──Pattern:
                                                          └──Type expr: Constructor: var
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Free
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: string
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: var
                                                             └──Pattern:
                                                                └──Type expr: Constructor: string
                                                                └──Desc: Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Var
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: var
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: expr
                                                       └──Expression:
                                                          └──Type expr: Constructor: var
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Free
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: string
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: var
                                                             └──Expression:
                                                                └──Type expr: Constructor: string
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Var
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: var
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: expr
                                                       └──Pattern:
                                                          └──Type expr: Constructor: var
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Bound
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: int
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: var
                                                             └──Pattern:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable: j
                                                 └──Expression:
                                                    └──Type expr: Constructor: expr
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
                                                                      └──Desc: Variable
                                                                         └──Variable: lt
                                                                         └──Type expr: Constructor: int
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Variable
                                                                         └──Variable: j
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: i
                                                       └──Expression:
                                                          └──Type expr: Constructor: expr
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Var
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: var
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: expr
                                                             └──Expression:
                                                                └──Type expr: Constructor: var
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Bound
                                                                      └──Constructor argument type:
                                                                         └──Type expr: Constructor: int
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: var
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Variable
                                                                         └──Variable: j
                                                       └──Expression:
                                                          └──Type expr: Constructor: expr
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
                                                                            └──Desc: Variable
                                                                               └──Variable: eq
                                                                               └──Type expr: Constructor: int
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: int
                                                                            └──Desc: Variable
                                                                               └──Variable: j
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Variable
                                                                         └──Variable: i
                                                             └──Expression:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: expr
                                                                         └──Type expr: Constructor: expr
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: int
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: expr
                                                                                  └──Type expr: Constructor: expr
                                                                            └──Desc: Variable
                                                                               └──Variable: shift
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: int
                                                                            └──Desc: Variable
                                                                               └──Variable: i
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: expr
                                                                      └──Desc: Variable
                                                                         └──Variable: iexp
                                                             └──Expression:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Var
                                                                      └──Constructor argument type:
                                                                         └──Type expr: Constructor: var
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: expr
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: var
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Bound
                                                                            └──Constructor argument type:
                                                                               └──Type expr: Constructor: int
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: var
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
                                                                                           └──Variable: j
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: int
                                                                                  └──Desc: Constant: 1
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fun
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: string
                                                                └──Type expr: Constructor: expr
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: expr
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: string
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: string
                                                                └──Desc: Variable: x
                                                             └──Pattern:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Variable: exp
                                                 └──Expression:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fun
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: string
                                                                └──Type expr: Constructor: expr
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: expr
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: string
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Constructor: string
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: expr
                                                                         └──Type expr: Constructor: expr
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: expr
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: expr
                                                                                  └──Type expr: Constructor: expr
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: int
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: expr
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Constructor: expr
                                                                                           └──Type expr: Constructor: expr
                                                                                  └──Desc: Variable
                                                                                     └──Variable: subst
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
                                                                                                 └──Variable: i
                                                                                     └──Expression:
                                                                                        └──Type expr: Constructor: int
                                                                                        └──Desc: Constant: 1
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: expr
                                                                            └──Desc: Variable
                                                                               └──Variable: iexp
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: expr
                                                                      └──Desc: Variable
                                                                         └──Variable: exp
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: App
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: expr
                                                                └──Type expr: Constructor: expr
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: expr
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: expr
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Variable: exp1
                                                             └──Pattern:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Variable: exp2
                                                 └──Expression:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: App
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: expr
                                                                └──Type expr: Constructor: expr
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: expr
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: expr
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: expr
                                                                         └──Type expr: Constructor: expr
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: expr
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: expr
                                                                                  └──Type expr: Constructor: expr
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: int
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: expr
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Constructor: expr
                                                                                           └──Type expr: Constructor: expr
                                                                                  └──Desc: Variable
                                                                                     └──Variable: subst
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: int
                                                                                  └──Desc: Variable
                                                                                     └──Variable: i
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: expr
                                                                            └──Desc: Variable
                                                                               └──Variable: iexp
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: expr
                                                                      └──Desc: Variable
                                                                         └──Variable: exp1
                                                             └──Expression:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: expr
                                                                         └──Type expr: Constructor: expr
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: expr
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: expr
                                                                                  └──Type expr: Constructor: expr
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: int
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: expr
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Constructor: expr
                                                                                           └──Type expr: Constructor: expr
                                                                                  └──Desc: Variable
                                                                                     └──Variable: subst
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: int
                                                                                  └──Desc: Variable
                                                                                     └──Variable: i
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: expr
                                                                            └──Desc: Variable
                                                                               └──Variable: exp
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: expr
                                                                      └──Desc: Variable
                                                                         └──Variable: exp2
       └──Structure item: Primitive
          └──Value description:
             └──Name: lookup
             └──Scheme:
                └──Variables:
                └──Type expr: Arrow
                   └──Type expr: Constructor: list
                      └──Type expr: Tuple
                         └──Type expr: Constructor: string
                         └──Type expr: Constructor: expr
                   └──Type expr: Arrow
                      └──Type expr: Constructor: string
                      └──Type expr: Constructor: option
                         └──Type expr: Constructor: expr
             └──Primitive name: %lookup
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: inst
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: list
                            └──Type expr: Tuple
                               └──Type expr: Constructor: string
                               └──Type expr: Constructor: expr
                         └──Type expr: Arrow
                            └──Type expr: Constructor: expr
                            └──Type expr: Constructor: expr
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: list
                               └──Type expr: Tuple
                                  └──Type expr: Constructor: string
                                  └──Type expr: Constructor: expr
                            └──Desc: Variable: env
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: expr
                               └──Type expr: Constructor: expr
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: expr
                                  └──Desc: Variable: exp
                               └──Expression:
                                  └──Type expr: Constructor: expr
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Variable
                                           └──Variable: exp
                                     └──Type expr: Constructor: expr
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: expr
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: var
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: expr
                                                 └──Pattern:
                                                    └──Type expr: Constructor: var
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Free
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: string
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: var
                                                       └──Pattern:
                                                          └──Type expr: Constructor: string
                                                          └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: expr
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: expr
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: string
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: expr
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Constructor: string
                                                                         └──Type expr: Constructor: expr
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: string
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: expr
                                                                └──Desc: Variable
                                                                   └──Variable: lookup
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: string
                                                                      └──Type expr: Constructor: expr
                                                                └──Desc: Variable
                                                                   └──Variable: env
                                                       └──Expression:
                                                          └──Type expr: Constructor: string
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Constructor: expr
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Some
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: expr
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: expr
                                                             └──Pattern:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Variable: exp
                                                       └──Expression:
                                                          └──Type expr: Constructor: expr
                                                          └──Desc: Variable
                                                             └──Variable: exp
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: None
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: expr
                                                       └──Expression:
                                                          └──Type expr: Constructor: expr
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Var
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: var
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: expr
                                                             └──Expression:
                                                                └──Type expr: Constructor: var
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Free
                                                                      └──Constructor argument type:
                                                                         └──Type expr: Constructor: string
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: var
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: string
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: expr
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: var
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: expr
                                                 └──Pattern:
                                                    └──Type expr: Constructor: var
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Bound
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: var
                                                       └──Pattern:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable: i
                                           └──Expression:
                                              └──Type expr: Constructor: expr
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: var
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: expr
                                                 └──Expression:
                                                    └──Type expr: Constructor: var
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Bound
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: var
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: i
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: expr
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fun
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: string
                                                          └──Type expr: Constructor: expr
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: expr
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: string
                                                       └──Type expr: Constructor: expr
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: string
                                                          └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: expr
                                                          └──Desc: Variable: exp
                                           └──Expression:
                                              └──Type expr: Constructor: expr
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fun
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: string
                                                          └──Type expr: Constructor: expr
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: expr
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: string
                                                       └──Type expr: Constructor: expr
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: string
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: expr
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: expr
                                                                   └──Type expr: Constructor: expr
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Constructor: string
                                                                               └──Type expr: Constructor: expr
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: expr
                                                                            └──Type expr: Constructor: expr
                                                                      └──Desc: Variable
                                                                         └──Variable: inst
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Constructor: string
                                                                            └──Type expr: Constructor: expr
                                                                      └──Desc: Variable
                                                                         └──Variable: env
                                                             └──Expression:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Variable
                                                                   └──Variable: exp
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: expr
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: App
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: expr
                                                          └──Type expr: Constructor: expr
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: expr
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: expr
                                                       └──Type expr: Constructor: expr
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: expr
                                                          └──Desc: Variable: exp1
                                                       └──Pattern:
                                                          └──Type expr: Constructor: expr
                                                          └──Desc: Variable: exp2
                                           └──Expression:
                                              └──Type expr: Constructor: expr
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: App
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: expr
                                                          └──Type expr: Constructor: expr
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: expr
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: expr
                                                       └──Type expr: Constructor: expr
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: expr
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: expr
                                                                   └──Type expr: Constructor: expr
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Constructor: string
                                                                               └──Type expr: Constructor: expr
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: expr
                                                                            └──Type expr: Constructor: expr
                                                                      └──Desc: Variable
                                                                         └──Variable: inst
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Constructor: string
                                                                            └──Type expr: Constructor: expr
                                                                      └──Desc: Variable
                                                                         └──Variable: env
                                                             └──Expression:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Variable
                                                                   └──Variable: exp1
                                                       └──Expression:
                                                          └──Type expr: Constructor: expr
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: expr
                                                                   └──Type expr: Constructor: expr
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Constructor: string
                                                                               └──Type expr: Constructor: expr
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: expr
                                                                            └──Type expr: Constructor: expr
                                                                      └──Desc: Variable
                                                                         └──Variable: inst
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Constructor: string
                                                                            └──Type expr: Constructor: expr
                                                                      └──Desc: Variable
                                                                         └──Variable: env
                                                             └──Expression:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Variable
                                                                   └──Variable: exp2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: eval
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: expr
                         └──Type expr: Constructor: expr
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: expr
                            └──Desc: Variable: exp
                         └──Expression:
                            └──Type expr: Constructor: expr
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: expr
                                  └──Desc: Variable
                                     └──Variable: exp
                               └──Type expr: Constructor: expr
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: App
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: expr
                                                    └──Type expr: Constructor: expr
                                              └──Constructor type:
                                                 └──Type expr: Constructor: expr
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: expr
                                                 └──Type expr: Constructor: expr
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Variable: exp1
                                                 └──Pattern:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Variable: exp2
                                     └──Expression:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: expr
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: expr
                                                       └──Type expr: Constructor: expr
                                                    └──Desc: Variable
                                                       └──Variable: eval
                                                 └──Expression:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Variable
                                                       └──Variable: exp1
                                           └──Type expr: Constructor: expr
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fun
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: string
                                                                └──Type expr: Constructor: expr
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: expr
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: string
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: string
                                                                └──Desc: Variable: x
                                                             └──Pattern:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Variable: exp
                                                 └──Expression:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: expr
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Variable
                                                             └──Variable: eval
                                                       └──Expression:
                                                          └──Type expr: Constructor: expr
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: expr
                                                                   └──Type expr: Constructor: expr
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: expr
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: expr
                                                                            └──Type expr: Constructor: expr
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: int
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: expr
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: expr
                                                                                     └──Type expr: Constructor: expr
                                                                            └──Desc: Variable
                                                                               └──Variable: subst
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: int
                                                                            └──Desc: Constant: 0
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: expr
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: expr
                                                                               └──Type expr: Constructor: expr
                                                                            └──Desc: Variable
                                                                               └──Variable: eval
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: expr
                                                                            └──Desc: Variable
                                                                               └──Variable: exp2
                                                             └──Expression:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Variable
                                                                   └──Variable: exp
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Variable: exp1
                                                 └──Expression:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: App
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: expr
                                                                └──Type expr: Constructor: expr
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: expr
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: expr
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Variable
                                                                   └──Variable: exp1
                                                             └──Expression:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: expr
                                                                         └──Type expr: Constructor: expr
                                                                      └──Desc: Variable
                                                                         └──Variable: eval
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: expr
                                                                      └──Desc: Variable
                                                                         └──Variable: exp2
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Variable: exp
                                     └──Expression:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Variable
                                           └──Variable: exp
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: bodies
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: expr
                         └──Type expr: Constructor: expr
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: expr
                            └──Desc: Variable: exp
                         └──Expression:
                            └──Type expr: Constructor: expr
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: expr
                                     └──Type expr: Constructor: expr
                                  └──Desc: Variable
                                     └──Variable: bodies
                               └──Expression:
                                  └──Type expr: Constructor: expr
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: expr
                                           └──Type expr: Constructor: expr
                                        └──Desc: Variable
                                           └──Variable: eval
                                     └──Expression:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Variable
                                           └──Variable: exp
             └──Value binding:
                └──Variable: by_value
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: expr
                         └──Type expr: Constructor: expr
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: expr
                            └──Desc: Variable: exp
                         └──Expression:
                            └──Type expr: Constructor: expr
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: expr
                                  └──Desc: Variable
                                     └──Variable: exp
                               └──Type expr: Constructor: expr
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fun
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: string
                                                    └──Type expr: Constructor: expr
                                              └──Constructor type:
                                                 └──Type expr: Constructor: expr
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: string
                                                 └──Type expr: Constructor: expr
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: string
                                                    └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Variable: exp
                                     └──Expression:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fun
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: string
                                                    └──Type expr: Constructor: expr
                                              └──Constructor type:
                                                 └──Type expr: Constructor: expr
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: string
                                                 └──Type expr: Constructor: expr
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: string
                                                    └──Desc: Variable
                                                       └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: expr
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Variable
                                                             └──Variable: by_value
                                                       └──Expression:
                                                          └──Type expr: Constructor: expr
                                                          └──Desc: Variable
                                                             └──Variable: exp
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: App
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: expr
                                                    └──Type expr: Constructor: expr
                                              └──Constructor type:
                                                 └──Type expr: Constructor: expr
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: expr
                                                 └──Type expr: Constructor: expr
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Variable: exp1
                                                 └──Pattern:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Variable: exp2
                                     └──Expression:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: App
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: expr
                                                    └──Type expr: Constructor: expr
                                              └──Constructor type:
                                                 └──Type expr: Constructor: expr
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: expr
                                                 └──Type expr: Constructor: expr
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: expr
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Variable
                                                             └──Variable: bodies
                                                       └──Expression:
                                                          └──Type expr: Constructor: expr
                                                          └──Desc: Variable
                                                             └──Variable: exp1
                                                 └──Expression:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Variable
                                                       └──Variable: exp2
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Variable: exp
                                     └──Expression:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Variable
                                           └──Variable: exp
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: head_nf
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: expr
                         └──Type expr: Constructor: expr
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: expr
                            └──Desc: Variable: exp
                         └──Expression:
                            └──Type expr: Constructor: expr
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: expr
                                  └──Desc: Variable
                                     └──Variable: exp
                               └──Type expr: Constructor: expr
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fun
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: string
                                                    └──Type expr: Constructor: expr
                                              └──Constructor type:
                                                 └──Type expr: Constructor: expr
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: string
                                                 └──Type expr: Constructor: expr
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: string
                                                    └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Variable: exp
                                     └──Expression:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fun
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: string
                                                    └──Type expr: Constructor: expr
                                              └──Constructor type:
                                                 └──Type expr: Constructor: expr
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: string
                                                 └──Type expr: Constructor: expr
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: string
                                                    └──Desc: Variable
                                                       └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: expr
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Variable
                                                             └──Variable: head_nf
                                                       └──Expression:
                                                          └──Type expr: Constructor: expr
                                                          └──Desc: Variable
                                                             └──Variable: exp
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: App
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: expr
                                                    └──Type expr: Constructor: expr
                                              └──Constructor type:
                                                 └──Type expr: Constructor: expr
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: expr
                                                 └──Type expr: Constructor: expr
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Variable: exp1
                                                 └──Pattern:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Variable: exp2
                                     └──Expression:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: expr
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: expr
                                                       └──Type expr: Constructor: expr
                                                    └──Desc: Variable
                                                       └──Variable: head_nf
                                                 └──Expression:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Variable
                                                       └──Variable: exp1
                                           └──Type expr: Constructor: expr
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fun
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: string
                                                                └──Type expr: Constructor: expr
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: expr
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: string
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: string
                                                                └──Desc: Variable: x
                                                             └──Pattern:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Variable: exp
                                                 └──Expression:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: expr
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Variable
                                                             └──Variable: head_nf
                                                       └──Expression:
                                                          └──Type expr: Constructor: expr
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: expr
                                                                   └──Type expr: Constructor: expr
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: expr
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: expr
                                                                            └──Type expr: Constructor: expr
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: int
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: expr
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: expr
                                                                                     └──Type expr: Constructor: expr
                                                                            └──Desc: Variable
                                                                               └──Variable: subst
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: int
                                                                            └──Desc: Constant: 0
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: expr
                                                                      └──Desc: Variable
                                                                         └──Variable: exp2
                                                             └──Expression:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Variable
                                                                   └──Variable: exp
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Variable: exp1
                                                 └──Expression:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: App
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: expr
                                                                └──Type expr: Constructor: expr
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: expr
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: expr
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Variable
                                                                   └──Variable: exp1
                                                             └──Expression:
                                                                └──Type expr: Constructor: expr
                                                                └──Desc: Variable
                                                                   └──Variable: exp2
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Variable: exp
                                     └──Expression:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Variable
                                           └──Variable: exp
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: args
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: expr
                         └──Type expr: Constructor: expr
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: expr
                            └──Desc: Variable: exp
                         └──Expression:
                            └──Type expr: Constructor: expr
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: expr
                                     └──Type expr: Constructor: expr
                                  └──Desc: Variable
                                     └──Variable: args
                               └──Expression:
                                  └──Type expr: Constructor: expr
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: expr
                                           └──Type expr: Constructor: expr
                                        └──Desc: Variable
                                           └──Variable: head_nf
                                     └──Expression:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Variable
                                           └──Variable: exp
             └──Value binding:
                └──Variable: by_name
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: expr
                         └──Type expr: Constructor: expr
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: expr
                            └──Desc: Variable: exp
                         └──Expression:
                            └──Type expr: Constructor: expr
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: expr
                                  └──Desc: Variable
                                     └──Variable: exp
                               └──Type expr: Constructor: expr
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fun
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: string
                                                    └──Type expr: Constructor: expr
                                              └──Constructor type:
                                                 └──Type expr: Constructor: expr
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: string
                                                 └──Type expr: Constructor: expr
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: string
                                                    └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Variable: exp
                                     └──Expression:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fun
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: string
                                                    └──Type expr: Constructor: expr
                                              └──Constructor type:
                                                 └──Type expr: Constructor: expr
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: string
                                                 └──Type expr: Constructor: expr
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: string
                                                    └──Desc: Variable
                                                       └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: expr
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Variable
                                                             └──Variable: args
                                                       └──Expression:
                                                          └──Type expr: Constructor: expr
                                                          └──Desc: Variable
                                                             └──Variable: exp
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: App
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: expr
                                                    └──Type expr: Constructor: expr
                                              └──Constructor type:
                                                 └──Type expr: Constructor: expr
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: expr
                                                 └──Type expr: Constructor: expr
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Variable: exp1
                                                 └──Pattern:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Variable: exp2
                                     └──Expression:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: App
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: expr
                                                    └──Type expr: Constructor: expr
                                              └──Constructor type:
                                                 └──Type expr: Constructor: expr
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: expr
                                                 └──Type expr: Constructor: expr
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: expr
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Variable
                                                             └──Variable: args
                                                       └──Expression:
                                                          └──Type expr: Constructor: expr
                                                          └──Desc: Variable
                                                             └──Variable: exp1
                                                 └──Expression:
                                                    └──Type expr: Constructor: expr
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: expr
                                                             └──Type expr: Constructor: expr
                                                          └──Desc: Variable
                                                             └──Variable: by_name
                                                       └──Expression:
                                                          └──Type expr: Constructor: expr
                                                          └──Desc: Variable
                                                             └──Variable: exp2
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Variable: exp
                                     └──Expression:
                                        └──Type expr: Constructor: expr
                                        └──Desc: Variable
                                           └──Variable: exp |}]


let%expect_test "" =
  let str =
    {|
      let id = fun x -> x;;

      let id_ref = ref id;;

      let _ = 
         ((!id_ref) true, (!id_ref) 5)
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    ("Cannot unify types"
     ("Type_expr.decode type_expr1" (Type 18 (Former (Constr () bool))))
     ("Type_expr.decode type_expr2" (Type 45 (Former (Constr () int))))) |}]


let%expect_test "" =
  let str =
    {|
      let id = fun x -> x;;

      let not = fun b -> match b with (true -> false | false -> true);;

      let _ = 
         let id_ref = ref id in
         id_ref := not;
         (!id_ref) 5
      ;; 
    |}
  in
  print_infer_result str;
  [%expect
    {|
    ("Cannot unify types"
     ("Type_expr.decode type_expr1" (Type 19 (Former (Constr () bool))))
     ("Type_expr.decode type_expr2" (Type 62 (Former (Constr () int))))) |}]


let%expect_test "" =
  let str =
    {|
      let id = fun x -> x;;

      let not = fun b -> match b with (true -> false | false -> true);;

      let _ = 
         let id_ref = ref id in
         id_ref := not;
         (!id_ref) true
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 2
                      └──Type expr: Variable: 2
                   └──Desc: Variable: id
                └──Abstraction:
                   └──Variables: 2,2
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 2
                         └──Type expr: Variable: 2
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 2
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: 2
                            └──Desc: Variable
                               └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: bool
                      └──Type expr: Constructor: bool
                   └──Desc: Variable: not
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: bool
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: bool
                            └──Desc: Variable: b
                         └──Expression:
                            └──Type expr: Constructor: bool
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Variable
                                     └──Variable: b
                               └──Type expr: Constructor: bool
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: bool
                                        └──Desc: Constant: true
                                     └──Expression:
                                        └──Type expr: Constructor: bool
                                        └──Desc: Constant: false
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: bool
                                        └──Desc: Constant: false
                                     └──Expression:
                                        └──Type expr: Constructor: bool
                                        └──Desc: Constant: true
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: bool
                   └──Desc: Any
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: bool
                      └──Desc: Let
                         └──Value bindings:
                            └──Value binding:
                               └──Pattern:
                                  └──Type expr: Constructor: ref
                                     └──Type expr: Arrow
                                        └──Type expr: Constructor: bool
                                        └──Type expr: Constructor: bool
                                  └──Desc: Variable: id_ref
                               └──Abstraction:
                                  └──Variables:
                                  └──Expression:
                                     └──Type expr: Constructor: ref
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: bool
                                           └──Type expr: Constructor: bool
                                     └──Desc: Application
                                        └──Expression:
                                           └──Type expr: Arrow
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: bool
                                                 └──Type expr: Constructor: bool
                                              └──Type expr: Constructor: ref
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: bool
                                                    └──Type expr: Constructor: bool
                                           └──Desc: Primitive: ref
                                        └──Expression:
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: bool
                                              └──Type expr: Constructor: bool
                                           └──Desc: Variable
                                              └──Variable: id
                                              └──Type expr: Constructor: bool
                         └──Expression:
                            └──Type expr: Constructor: bool
                            └──Desc: Sequence
                               └──Expression:
                                  └──Type expr: Constructor: unit
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: bool
                                              └──Type expr: Constructor: bool
                                           └──Type expr: Constructor: unit
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: ref
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: bool
                                                       └──Type expr: Constructor: bool
                                                 └──Type expr: Arrow
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: bool
                                                       └──Type expr: Constructor: bool
                                                    └──Type expr: Constructor: unit
                                              └──Desc: Primitive: (:=)
                                           └──Expression:
                                              └──Type expr: Constructor: ref
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: bool
                                                    └──Type expr: Constructor: bool
                                              └──Desc: Variable
                                                 └──Variable: id_ref
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: bool
                                           └──Type expr: Constructor: bool
                                        └──Desc: Variable
                                           └──Variable: not
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: bool
                                           └──Type expr: Constructor: bool
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: ref
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: bool
                                                       └──Type expr: Constructor: bool
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: bool
                                                    └──Type expr: Constructor: bool
                                              └──Desc: Primitive: (!)
                                           └──Expression:
                                              └──Type expr: Constructor: ref
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: bool
                                                    └──Type expr: Constructor: bool
                                              └──Desc: Variable
                                                 └──Variable: id_ref
                                     └──Expression:
                                        └──Type expr: Constructor: bool
                                        └──Desc: Constant: true |}]


let%expect_test "" =
  let str =
    {|
      type 'a list =
        | Nil
        | Cons of 'a * 'a list
      ;;

      external fold_left : 'a 'b. ('b -> 'a -> 'b) -> 'b -> 'a list -> 'b = "%fold_left";;

      let length = fold_left (fun n _ -> n + 1) 0;;
      
      let length' = fun t -> fold_left (fun n _ -> n + 1) 0 t;;

      let t1 = Cons (1, Nil);;
      let t2 = Cons (true, Nil);;

      let _ = 
         (length t1, length t2)
      ;;

      let _ = 
         (length' t1, length' t2)
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    ("Cannot unify types"
     ("Type_expr.decode type_expr1"
      (Type 151 (Former (Constr ((Type 25 (Former (Constr () int)))) list))))
     ("Type_expr.decode type_expr2"
      (Type 154 (Former (Constr ((Type 155 (Former (Constr () bool)))) list))))) |}]
