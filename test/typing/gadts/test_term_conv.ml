open! Import
open Util

let%expect_test "term-conv-1" =
  let str = 
    {|
      type 'a ty = 
        | Int constraint 'a = int
        | String constraint 'a = string
        | List of 'b. 'b ty constraint 'a = 'b list
        | Pair of 'b 'c. 'b ty * 'c ty constraint 'a = 'b * 'c
        | Fun of 'b 'c. 'b ty * 'c ty constraint 'a = 'b -> 'c
      ;;

      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      exception Cast_failure;;

      let rec (type 't1 't2) check_eq = 
        fun (t1 : 't1 ty) (t2 : 't2 ty) ->
          (match (t1, t2) with  
           ( (Int, Int) -> Refl
           | (String, String) -> Refl
           | (List t1, List t2) ->
              (match check_eq t1 t2 with ( Refl -> Refl ))
           | (Pair (t11, t12), Pair (t21, t22)) ->
              (match (check_eq t11 t21, check_eq t12 t22) with ( (Refl, Refl) -> Refl ))
           | (Fun (t11, t12), Fun (t21, t22)) ->
              (match (check_eq t11 t21, check_eq t12 t22) with ( (Refl, Refl) -> Refl ))
           ) 
          : ('t1, 't2) eq)
      ;;

      let (type 't1 't2) cast = 
        fun (t1 : 't1 ty) (t2 : 't2 ty)  (x : 't1) ->
          (match check_eq t1 t2 with (Refl -> x) : 't2)
      ;;

      (* HOAS *)
      type 'a hterm = 
        | Tag of 'a ty * int
        | Con of 'a
        | Lam of 'b 'c. 'b ty * ('b hterm -> 'c hterm) constraint 'a = 'b -> 'c
        | App of 'b. ('b -> 'a) hterm * 'b hterm
      ;; 

      external fail_with : 'a. string -> 'a = "%fail_with";;

      let rec (type 't) heval = 
        fun (t : 't hterm) ->
          (match t with 
           ( Tag _ -> fail_with "HOAS eval"
           | Con v -> v
           | Lam (_, f) -> fun x -> heval (f (Con x))
           | App (f, x) -> heval f (heval x) 
           )
          : 't)
      ;;

      type ('env, 't) index = 
        | Zero of 'env1. unit constraint 'env = 'env1 * 't
        | Succ of 'env1 's. ('env1, 't) index constraint 'env = 'env1 * 's
      ;;

      let rec (type 'env 't) index_to_int = 
        fun (ix : ('env, 't) index) ->
          (match ix with 
           ( Zero () -> 0
           | Succ n -> index_to_int n + 1
           )
          : int)
      ;;

      type 'env stack = 
        | Empty constraint 'env = unit
        | Push of 'env1 't. 'env1 stack * 't constraint 'env = 'env1 * 't
      ;;

      let rec (type 'env 't) prj = 
        fun (ix : ('env, 't) index) (s : 'env stack) ->
          (match (ix, s) with 
           ( (Zero (), Push (_, v)) -> v
           | (Succ ix, Push (s, _)) -> prj ix s
           )
          : 't)
      ;;

      type ('env, 't) dterm = 
        | D_var of ('env, 't) index
        | D_con of 't
        | D_lam of 's 'r. ('env * 's, 'r) dterm constraint 't = 's -> 'r
        | D_app of 's. ('env, 's -> 't) dterm * ('env, 's) dterm  
      ;;

      let rec (type 'env 't) deval = 
        fun (t : ('env, 't) dterm) (s : 'env stack) ->
          (match t with 
           ( D_var ix -> prj ix s
           | D_con v -> v
           | D_lam b -> fun x -> deval b (Push (s, x))
           | D_app (f, x) -> deval f s (deval x s)
           )
          : 't)
      ;;

      (* Conversion between dterms and hterms *)

      type ('env1, 'env2) layout = 
        | Empty_layout constraint 'env2 = unit
        | Push_layout of 't 'env21. 't ty * ('env1, 'env21) layout * ('env1, 't) index constraint 'env2 = 'env21 * 't
      ;;

      let rec (type 'env1 'env2) size = 
        fun (l : ('env1, 'env2) layout) ->
          (match l with 
           ( Empty_layout -> 0
           | Push_layout (_, l, _) -> size l + 1
           )
          : int) 
      ;;

      let rec (type 'env1 'env2 't) inc = 
        fun (l : ('env1, 'env2) layout) ->
          (match l with
           ( Empty_layout -> Empty_layout
           | Push_layout (t, l, ix) -> Push_layout (t, inc l, Succ ix) 
           ) 
          : ('env1 * 't, 'env2) layout)
      ;;

      let rec (type 't 'env1 'env2) prjl = 
        fun (t : 't ty) (n : int) (l : ('env1, 'env2) layout) ->
          (match l with 
           ( Empty_layout -> fail_with "convert prjl"
           | Push_layout (t', l, ix) ->
              if n = 0 then
                (* Annotation added due to lack of propagation *)
                (match check_eq t t' with ( Refl -> (ix : ('env1, 't) index) ))
              else
                (prjl t (n - 1) l) 
           )
          : ('env1, 't) index) 
      ;;

      let rec (type 'env 't) convert = 
        fun (l : ('env, 'env) layout) (t : 't hterm) ->
          (match t with 
           ( Tag (t, sz) -> D_var (prjl t (((size l) - sz) - 1) l)
           | Con v -> D_con v
           | Lam (t, f) ->
              let l' = Push_layout (t, inc l, Zero ()) in
              D_lam (convert l' (f (Tag (t, size l))))
           | App (f, a) ->
              D_app (convert l f, convert l a)
           )
          : ('env, 't) dterm)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: ty
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Int
                   └──Constructor alphas: 2579
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 2579
                   └──Constraint:
                      └──Type expr: Variable: 2579
                      └──Type expr: Constructor: int
                └──Constructor declaration:
                   └──Constructor name: String
                   └──Constructor alphas: 2579
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 2579
                   └──Constraint:
                      └──Type expr: Variable: 2579
                      └──Type expr: Constructor: string
                └──Constructor declaration:
                   └──Constructor name: List
                   └──Constructor alphas: 2579
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 2579
                   └──Constructor argument:
                      └──Constructor betas: 2584
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 2584
                   └──Constraint:
                      └──Type expr: Variable: 2579
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 2584
                └──Constructor declaration:
                   └──Constructor name: Pair
                   └──Constructor alphas: 2579
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 2579
                   └──Constructor argument:
                      └──Constructor betas: 2589 2588
                      └──Type expr: Tuple
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 2588
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 2589
                   └──Constraint:
                      └──Type expr: Variable: 2579
                      └──Type expr: Tuple
                         └──Type expr: Variable: 2588
                         └──Type expr: Variable: 2589
                └──Constructor declaration:
                   └──Constructor name: Fun
                   └──Constructor alphas: 2579
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 2579
                   └──Constructor argument:
                      └──Constructor betas: 2596 2595
                      └──Type expr: Tuple
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 2595
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 2596
                   └──Constraint:
                      └──Type expr: Variable: 2579
                      └──Type expr: Arrow
                         └──Type expr: Variable: 2595
                         └──Type expr: Variable: 2596
       └──Structure item: Type
          └──Type declaration:
             └──Type name: eq
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Refl
                   └──Constructor alphas: 2602 2603
                   └──Constructor type:
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: 2602
                         └──Type expr: Variable: 2603
                   └──Constraint:
                      └──Type expr: Variable: 2602
                      └──Type expr: Variable: 2603
       └──Structure item: Exception
          └──Type exception:
             └──Extension constructor:
                └──Extension name: exn
                └──Extension parameters:
                └──Extension constructor kind: Declaration
                   └──Constructor declaration:
                      └──Constructor name: Cast_failure
                      └──Constructor alphas:
                      └──Constructor type:
                         └──Type expr: Constructor: exn
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: check_eq
                └──Abstraction:
                   └──Variables: 10,12
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 38
                         └──Type expr: Arrow
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: 48
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: 38
                               └──Type expr: Variable: 48
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: 38
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: ty
                                  └──Type expr: Variable: 48
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: 38
                                  └──Type expr: Variable: 48
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: ty
                                     └──Type expr: Variable: 48
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: 38
                                     └──Type expr: Variable: 48
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: ty
                                              └──Type expr: Variable: 38
                                           └──Type expr: Constructor: ty
                                              └──Type expr: Variable: 48
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: 38
                                              └──Desc: Variable
                                                 └──Variable: t1
                                           └──Expression:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: 48
                                              └──Desc: Variable
                                                 └──Variable: t2
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: ty
                                           └──Type expr: Variable: 38
                                        └──Type expr: Constructor: ty
                                           └──Type expr: Variable: 48
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 38
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 48
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 38
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 38
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 48
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 48
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: 38
                                                 └──Type expr: Variable: 48
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Refl
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: 38
                                                          └──Type expr: Variable: 38
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 38
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 48
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 38
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: String
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 38
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 48
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: String
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 48
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: 38
                                                 └──Type expr: Variable: 48
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Refl
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: 38
                                                          └──Type expr: Variable: 38
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 38
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 48
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 38
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: List
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 130
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 38
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: 130
                                                          └──Desc: Variable: t1
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 48
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: List
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 127
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 48
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: 127
                                                          └──Desc: Variable: t2
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: 38
                                                 └──Type expr: Variable: 48
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: 130
                                                       └──Type expr: Variable: 127
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 127
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: 130
                                                                └──Type expr: Variable: 127
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: 130
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: 127
                                                                      └──Type expr: Constructor: eq
                                                                         └──Type expr: Variable: 130
                                                                         └──Type expr: Variable: 127
                                                                └──Desc: Variable
                                                                   └──Variable: check_eq
                                                                   └──Type expr: Variable: 127
                                                                   └──Type expr: Variable: 130
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 130
                                                                └──Desc: Variable
                                                                   └──Variable: t1
                                                       └──Expression:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: 127
                                                          └──Desc: Variable
                                                             └──Variable: t2
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: 130
                                                    └──Type expr: Variable: 127
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: 130
                                                             └──Type expr: Variable: 127
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Refl
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: 130
                                                                      └──Type expr: Variable: 127
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: 38
                                                             └──Type expr: Variable: 48
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Refl
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: 38
                                                                      └──Type expr: Variable: 38
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 38
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 48
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 38
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Pair
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 212
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 210
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 38
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 212
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 210
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 212
                                                                └──Desc: Variable: t11
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 210
                                                                └──Desc: Variable: t12
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 48
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Pair
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 206
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 204
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 48
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 206
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 204
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 206
                                                                └──Desc: Variable: t21
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 204
                                                                └──Desc: Variable: t22
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: 38
                                                 └──Type expr: Variable: 48
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: 212
                                                          └──Type expr: Variable: 206
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: 210
                                                          └──Type expr: Variable: 204
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: 212
                                                             └──Type expr: Variable: 206
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: 206
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: 212
                                                                      └──Type expr: Variable: 206
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: 212
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: 206
                                                                            └──Type expr: Constructor: eq
                                                                               └──Type expr: Variable: 212
                                                                               └──Type expr: Variable: 206
                                                                      └──Desc: Variable
                                                                         └──Variable: check_eq
                                                                         └──Type expr: Variable: 206
                                                                         └──Type expr: Variable: 212
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: 212
                                                                      └──Desc: Variable
                                                                         └──Variable: t11
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 206
                                                                └──Desc: Variable
                                                                   └──Variable: t21
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: 210
                                                             └──Type expr: Variable: 204
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: 204
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: 210
                                                                      └──Type expr: Variable: 204
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: 210
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: 204
                                                                            └──Type expr: Constructor: eq
                                                                               └──Type expr: Variable: 210
                                                                               └──Type expr: Variable: 204
                                                                      └──Desc: Variable
                                                                         └──Variable: check_eq
                                                                         └──Type expr: Variable: 204
                                                                         └──Type expr: Variable: 210
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: 210
                                                                      └──Desc: Variable
                                                                         └──Variable: t12
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 204
                                                                └──Desc: Variable
                                                                   └──Variable: t22
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: 212
                                                       └──Type expr: Variable: 206
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: 210
                                                       └──Type expr: Variable: 204
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: 212
                                                                └──Type expr: Variable: 206
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: 210
                                                                └──Type expr: Variable: 204
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: 212
                                                                   └──Type expr: Variable: 206
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: 212
                                                                            └──Type expr: Variable: 206
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: 210
                                                                   └──Type expr: Variable: 204
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: 210
                                                                            └──Type expr: Variable: 204
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: 38
                                                             └──Type expr: Variable: 48
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Refl
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: 38
                                                                      └──Type expr: Variable: 38
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 38
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 48
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 38
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fun
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 333
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 331
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 38
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 333
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 331
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 333
                                                                └──Desc: Variable: t11
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 331
                                                                └──Desc: Variable: t12
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 48
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fun
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 327
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 325
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 48
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 327
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 325
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 327
                                                                └──Desc: Variable: t21
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 325
                                                                └──Desc: Variable: t22
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: 38
                                                 └──Type expr: Variable: 48
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: 333
                                                          └──Type expr: Variable: 327
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: 331
                                                          └──Type expr: Variable: 325
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: 333
                                                             └──Type expr: Variable: 327
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: 327
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: 333
                                                                      └──Type expr: Variable: 327
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: 333
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: 327
                                                                            └──Type expr: Constructor: eq
                                                                               └──Type expr: Variable: 333
                                                                               └──Type expr: Variable: 327
                                                                      └──Desc: Variable
                                                                         └──Variable: check_eq
                                                                         └──Type expr: Variable: 327
                                                                         └──Type expr: Variable: 333
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: 333
                                                                      └──Desc: Variable
                                                                         └──Variable: t11
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 327
                                                                └──Desc: Variable
                                                                   └──Variable: t21
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: 331
                                                             └──Type expr: Variable: 325
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: 325
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: 331
                                                                      └──Type expr: Variable: 325
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: 331
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: 325
                                                                            └──Type expr: Constructor: eq
                                                                               └──Type expr: Variable: 331
                                                                               └──Type expr: Variable: 325
                                                                      └──Desc: Variable
                                                                         └──Variable: check_eq
                                                                         └──Type expr: Variable: 325
                                                                         └──Type expr: Variable: 331
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: 331
                                                                      └──Desc: Variable
                                                                         └──Variable: t12
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 325
                                                                └──Desc: Variable
                                                                   └──Variable: t22
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: 333
                                                       └──Type expr: Variable: 327
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: 331
                                                       └──Type expr: Variable: 325
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: 333
                                                                └──Type expr: Variable: 327
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: 331
                                                                └──Type expr: Variable: 325
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: 333
                                                                   └──Type expr: Variable: 327
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: 333
                                                                            └──Type expr: Variable: 327
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: 331
                                                                   └──Type expr: Variable: 325
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: 331
                                                                            └──Type expr: Variable: 325
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: 38
                                                             └──Type expr: Variable: 48
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Refl
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: 38
                                                                      └──Type expr: Variable: 38
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 440
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 450
                         └──Type expr: Arrow
                            └──Type expr: Variable: 440
                            └──Type expr: Variable: 450
                   └──Desc: Variable: cast
                └──Abstraction:
                   └──Variables: 440,450
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 440
                         └──Type expr: Arrow
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: 450
                            └──Type expr: Arrow
                               └──Type expr: Variable: 440
                               └──Type expr: Variable: 450
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: 440
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: ty
                                  └──Type expr: Variable: 450
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 440
                                  └──Type expr: Variable: 450
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: ty
                                     └──Type expr: Variable: 450
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 440
                                     └──Type expr: Variable: 450
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: 440
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: 450
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: 440
                                                 └──Type expr: Variable: 450
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: 450
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: 440
                                                          └──Type expr: Variable: 450
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 440
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 450
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: 440
                                                                   └──Type expr: Variable: 450
                                                          └──Desc: Variable
                                                             └──Variable: check_eq
                                                             └──Type expr: Variable: 450
                                                             └──Type expr: Variable: 440
                                                       └──Expression:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: 440
                                                          └──Desc: Variable
                                                             └──Variable: t1
                                                 └──Expression:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 450
                                                    └──Desc: Variable
                                                       └──Variable: t2
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: 440
                                              └──Type expr: Variable: 450
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: 440
                                                       └──Type expr: Variable: 450
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Refl
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: 440
                                                                └──Type expr: Variable: 450
                                                 └──Expression:
                                                    └──Type expr: Variable: 450
                                                    └──Desc: Variable
                                                       └──Variable: x
       └──Structure item: Type
          └──Type declaration:
             └──Type name: hterm
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Tag
                   └──Constructor alphas: 2606
                   └──Constructor type:
                      └──Type expr: Constructor: hterm
                         └──Type expr: Variable: 2606
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 2606
                         └──Type expr: Constructor: int
                └──Constructor declaration:
                   └──Constructor name: Con
                   └──Constructor alphas: 2606
                   └──Constructor type:
                      └──Type expr: Constructor: hterm
                         └──Type expr: Variable: 2606
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: 2606
                └──Constructor declaration:
                   └──Constructor name: Lam
                   └──Constructor alphas: 2606
                   └──Constructor type:
                      └──Type expr: Constructor: hterm
                         └──Type expr: Variable: 2606
                   └──Constructor argument:
                      └──Constructor betas: 2613 2612
                      └──Type expr: Tuple
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 2612
                         └──Type expr: Arrow
                            └──Type expr: Constructor: hterm
                               └──Type expr: Variable: 2612
                            └──Type expr: Constructor: hterm
                               └──Type expr: Variable: 2613
                   └──Constraint:
                      └──Type expr: Variable: 2606
                      └──Type expr: Arrow
                         └──Type expr: Variable: 2612
                         └──Type expr: Variable: 2613
                └──Constructor declaration:
                   └──Constructor name: App
                   └──Constructor alphas: 2606
                   └──Constructor type:
                      └──Type expr: Constructor: hterm
                         └──Type expr: Variable: 2606
                   └──Constructor argument:
                      └──Constructor betas: 2621
                      └──Type expr: Tuple
                         └──Type expr: Constructor: hterm
                            └──Type expr: Arrow
                               └──Type expr: Variable: 2621
                               └──Type expr: Variable: 2606
                         └──Type expr: Constructor: hterm
                            └──Type expr: Variable: 2621
       └──Structure item: Primitive
          └──Value description:
             └──Name: fail_with
             └──Scheme:
                └──Variables: 490
                └──Type expr: Arrow
                   └──Type expr: Constructor: string
                   └──Type expr: Variable: 490
             └──Primitive name: %fail_with
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: heval
                └──Abstraction:
                   └──Variables: 499
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: hterm
                            └──Type expr: Variable: 516
                         └──Type expr: Variable: 516
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: hterm
                               └──Type expr: Variable: 516
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Variable: 516
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: hterm
                                     └──Type expr: Variable: 516
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: hterm
                                  └──Type expr: Variable: 516
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: 516
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Tag
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 516
                                                    └──Type expr: Constructor: int
                                              └──Constructor type:
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: 516
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 516
                                                 └──Type expr: Constructor: int
                                              └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Variable: 516
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: string
                                                 └──Type expr: Variable: 516
                                              └──Desc: Variable
                                                 └──Variable: fail_with
                                                 └──Type expr: Variable: 516
                                           └──Expression:
                                              └──Type expr: Constructor: string
                                              └──Desc: Constant: HOAS eval
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: 516
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Con
                                              └──Constructor argument type:
                                                 └──Type expr: Variable: 516
                                              └──Constructor type:
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: 516
                                           └──Pattern:
                                              └──Type expr: Variable: 516
                                              └──Desc: Variable: v
                                     └──Expression:
                                        └──Type expr: Variable: 516
                                        └──Desc: Variable
                                           └──Variable: v
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: 516
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Lam
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 565
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: 565
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: 561
                                              └──Constructor type:
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: 516
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 565
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: 565
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: 561
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 565
                                                    └──Desc: Any
                                                 └──Pattern:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: 565
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: 561
                                                    └──Desc: Variable: f
                                     └──Expression:
                                        └──Type expr: Variable: 516
                                        └──Desc: Function
                                           └──Pattern:
                                              └──Type expr: Variable: 565
                                              └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Variable: 561
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: 561
                                                       └──Type expr: Variable: 561
                                                    └──Desc: Variable
                                                       └──Variable: heval
                                                       └──Type expr: Variable: 561
                                                 └──Expression:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: 561
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: 565
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: 561
                                                          └──Desc: Variable
                                                             └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: 565
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Con
                                                                └──Constructor argument type:
                                                                   └──Type expr: Variable: 565
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: hterm
                                                                      └──Type expr: Variable: 565
                                                             └──Expression:
                                                                └──Type expr: Variable: 565
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: 516
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: App
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: 613
                                                          └──Type expr: Variable: 516
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: 613
                                              └──Constructor type:
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: 516
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 613
                                                       └──Type expr: Variable: 516
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: 613
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: 613
                                                          └──Type expr: Variable: 516
                                                    └──Desc: Variable: f
                                                 └──Pattern:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: 613
                                                    └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: 516
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: 613
                                                 └──Type expr: Variable: 516
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 613
                                                             └──Type expr: Variable: 516
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: 613
                                                          └──Type expr: Variable: 516
                                                    └──Desc: Variable
                                                       └──Variable: heval
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: 613
                                                          └──Type expr: Variable: 516
                                                 └──Expression:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: 613
                                                          └──Type expr: Variable: 516
                                                    └──Desc: Variable
                                                       └──Variable: f
                                           └──Expression:
                                              └──Type expr: Variable: 613
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: 613
                                                       └──Type expr: Variable: 613
                                                    └──Desc: Variable
                                                       └──Variable: heval
                                                       └──Type expr: Variable: 613
                                                 └──Expression:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: 613
                                                    └──Desc: Variable
                                                       └──Variable: x
       └──Structure item: Type
          └──Type declaration:
             └──Type name: index
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Zero
                   └──Constructor alphas: 2627 2628
                   └──Constructor type:
                      └──Type expr: Constructor: index
                         └──Type expr: Variable: 2627
                         └──Type expr: Variable: 2628
                   └──Constructor argument:
                      └──Constructor betas: 2629
                      └──Type expr: Constructor: unit
                   └──Constraint:
                      └──Type expr: Variable: 2627
                      └──Type expr: Tuple
                         └──Type expr: Variable: 2629
                         └──Type expr: Variable: 2628
                └──Constructor declaration:
                   └──Constructor name: Succ
                   └──Constructor alphas: 2627 2628
                   └──Constructor type:
                      └──Type expr: Constructor: index
                         └──Type expr: Variable: 2627
                         └──Type expr: Variable: 2628
                   └──Constructor argument:
                      └──Constructor betas: 2634 2633
                      └──Type expr: Constructor: index
                         └──Type expr: Variable: 2633
                         └──Type expr: Variable: 2628
                   └──Constraint:
                      └──Type expr: Variable: 2627
                      └──Type expr: Tuple
                         └──Type expr: Variable: 2633
                         └──Type expr: Variable: 2634
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: index_to_int
                └──Abstraction:
                   └──Variables: 650,649
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: index
                            └──Type expr: Variable: 671
                            └──Type expr: Variable: 672
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: index
                               └──Type expr: Variable: 671
                               └──Type expr: Variable: 672
                            └──Desc: Variable: ix
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: index
                                     └──Type expr: Variable: 671
                                     └──Type expr: Variable: 672
                                  └──Desc: Variable
                                     └──Variable: ix
                               └──Type expr: Constructor: index
                                  └──Type expr: Variable: 671
                                  └──Type expr: Variable: 672
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: index
                                           └──Type expr: Variable: 671
                                           └──Type expr: Variable: 672
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Zero
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: 671
                                                    └──Type expr: Variable: 672
                                           └──Pattern:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 0
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: index
                                           └──Type expr: Variable: 671
                                           └──Type expr: Variable: 672
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: 701
                                                    └──Type expr: Variable: 672
                                              └──Constructor type:
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: 671
                                                    └──Type expr: Variable: 672
                                           └──Pattern:
                                              └──Type expr: Constructor: index
                                                 └──Type expr: Variable: 701
                                                 └──Type expr: Variable: 672
                                              └──Desc: Variable: n
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
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: 701
                                                                └──Type expr: Variable: 672
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: index_to_int
                                                             └──Type expr: Variable: 672
                                                             └──Type expr: Variable: 701
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: 701
                                                             └──Type expr: Variable: 672
                                                          └──Desc: Variable
                                                             └──Variable: n
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 1
       └──Structure item: Type
          └──Type declaration:
             └──Type name: stack
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Empty
                   └──Constructor alphas: 2638
                   └──Constructor type:
                      └──Type expr: Constructor: stack
                         └──Type expr: Variable: 2638
                   └──Constraint:
                      └──Type expr: Variable: 2638
                      └──Type expr: Constructor: unit
                └──Constructor declaration:
                   └──Constructor name: Push
                   └──Constructor alphas: 2638
                   └──Constructor type:
                      └──Type expr: Constructor: stack
                         └──Type expr: Variable: 2638
                   └──Constructor argument:
                      └──Constructor betas: 2642 2641
                      └──Type expr: Tuple
                         └──Type expr: Constructor: stack
                            └──Type expr: Variable: 2641
                         └──Type expr: Variable: 2642
                   └──Constraint:
                      └──Type expr: Variable: 2638
                      └──Type expr: Tuple
                         └──Type expr: Variable: 2641
                         └──Type expr: Variable: 2642
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: prj
                └──Abstraction:
                   └──Variables: 750,749
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: index
                            └──Type expr: Variable: 775
                            └──Type expr: Variable: 776
                         └──Type expr: Arrow
                            └──Type expr: Constructor: stack
                               └──Type expr: Variable: 775
                            └──Type expr: Variable: 776
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: index
                               └──Type expr: Variable: 775
                               └──Type expr: Variable: 776
                            └──Desc: Variable: ix
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: stack
                                  └──Type expr: Variable: 775
                               └──Type expr: Variable: 776
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: stack
                                     └──Type expr: Variable: 775
                                  └──Desc: Variable: s
                               └──Expression:
                                  └──Type expr: Variable: 776
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: index
                                              └──Type expr: Variable: 775
                                              └──Type expr: Variable: 776
                                           └──Type expr: Constructor: stack
                                              └──Type expr: Variable: 775
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: index
                                                 └──Type expr: Variable: 775
                                                 └──Type expr: Variable: 776
                                              └──Desc: Variable
                                                 └──Variable: ix
                                           └──Expression:
                                              └──Type expr: Constructor: stack
                                                 └──Type expr: Variable: 775
                                              └──Desc: Variable
                                                 └──Variable: s
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: index
                                           └──Type expr: Variable: 775
                                           └──Type expr: Variable: 776
                                        └──Type expr: Constructor: stack
                                           └──Type expr: Variable: 775
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: 775
                                                    └──Type expr: Variable: 776
                                                 └──Type expr: Constructor: stack
                                                    └──Type expr: Variable: 775
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: 775
                                                       └──Type expr: Variable: 776
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: 775
                                                                └──Type expr: Variable: 776
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                                 └──Pattern:
                                                    └──Type expr: Constructor: stack
                                                       └──Type expr: Variable: 775
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Push
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: 813
                                                                └──Type expr: Variable: 811
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: 775
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: 813
                                                             └──Type expr: Variable: 811
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: 813
                                                                └──Desc: Any
                                                             └──Pattern:
                                                                └──Type expr: Variable: 811
                                                                └──Desc: Variable: v
                                           └──Expression:
                                              └──Type expr: Variable: 776
                                              └──Desc: Variable
                                                 └──Variable: v
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: 775
                                                    └──Type expr: Variable: 776
                                                 └──Type expr: Constructor: stack
                                                    └──Type expr: Variable: 775
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: 775
                                                       └──Type expr: Variable: 776
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: 851
                                                                └──Type expr: Variable: 776
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: 775
                                                                └──Type expr: Variable: 776
                                                       └──Pattern:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: 851
                                                             └──Type expr: Variable: 776
                                                          └──Desc: Variable: ix
                                                 └──Pattern:
                                                    └──Type expr: Constructor: stack
                                                       └──Type expr: Variable: 775
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Push
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: 848
                                                                └──Type expr: Variable: 846
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: 775
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: 848
                                                             └──Type expr: Variable: 846
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: 848
                                                                └──Desc: Variable: s
                                                             └──Pattern:
                                                                └──Type expr: Variable: 846
                                                                └──Desc: Any
                                           └──Expression:
                                              └──Type expr: Variable: 776
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: stack
                                                          └──Type expr: Variable: 848
                                                       └──Type expr: Variable: 776
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: 848
                                                                └──Type expr: Variable: 776
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: 848
                                                                └──Type expr: Variable: 776
                                                          └──Desc: Variable
                                                             └──Variable: prj
                                                             └──Type expr: Variable: 776
                                                             └──Type expr: Variable: 848
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: 848
                                                             └──Type expr: Variable: 776
                                                          └──Desc: Variable
                                                             └──Variable: ix
                                                 └──Expression:
                                                    └──Type expr: Constructor: stack
                                                       └──Type expr: Variable: 848
                                                    └──Desc: Variable
                                                       └──Variable: s
       └──Structure item: Type
          └──Type declaration:
             └──Type name: dterm
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: D_var
                   └──Constructor alphas: 2647 2648
                   └──Constructor type:
                      └──Type expr: Constructor: dterm
                         └──Type expr: Variable: 2647
                         └──Type expr: Variable: 2648
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: index
                         └──Type expr: Variable: 2647
                         └──Type expr: Variable: 2648
                └──Constructor declaration:
                   └──Constructor name: D_con
                   └──Constructor alphas: 2647 2648
                   └──Constructor type:
                      └──Type expr: Constructor: dterm
                         └──Type expr: Variable: 2647
                         └──Type expr: Variable: 2648
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: 2648
                └──Constructor declaration:
                   └──Constructor name: D_lam
                   └──Constructor alphas: 2647 2648
                   └──Constructor type:
                      └──Type expr: Constructor: dterm
                         └──Type expr: Variable: 2647
                         └──Type expr: Variable: 2648
                   └──Constructor argument:
                      └──Constructor betas: 2653 2652
                      └──Type expr: Constructor: dterm
                         └──Type expr: Tuple
                            └──Type expr: Variable: 2647
                            └──Type expr: Variable: 2652
                         └──Type expr: Variable: 2653
                   └──Constraint:
                      └──Type expr: Variable: 2648
                      └──Type expr: Arrow
                         └──Type expr: Variable: 2652
                         └──Type expr: Variable: 2653
                └──Constructor declaration:
                   └──Constructor name: D_app
                   └──Constructor alphas: 2647 2648
                   └──Constructor type:
                      └──Type expr: Constructor: dterm
                         └──Type expr: Variable: 2647
                         └──Type expr: Variable: 2648
                   └──Constructor argument:
                      └──Constructor betas: 2658
                      └──Type expr: Tuple
                         └──Type expr: Constructor: dterm
                            └──Type expr: Variable: 2647
                            └──Type expr: Arrow
                               └──Type expr: Variable: 2658
                               └──Type expr: Variable: 2648
                         └──Type expr: Constructor: dterm
                            └──Type expr: Variable: 2647
                            └──Type expr: Variable: 2658
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: deval
                └──Abstraction:
                   └──Variables: 896,895
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: dterm
                            └──Type expr: Variable: 921
                            └──Type expr: Variable: 922
                         └──Type expr: Arrow
                            └──Type expr: Constructor: stack
                               └──Type expr: Variable: 921
                            └──Type expr: Variable: 922
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: dterm
                               └──Type expr: Variable: 921
                               └──Type expr: Variable: 922
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: stack
                                  └──Type expr: Variable: 921
                               └──Type expr: Variable: 922
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: stack
                                     └──Type expr: Variable: 921
                                  └──Desc: Variable: s
                               └──Expression:
                                  └──Type expr: Variable: 922
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: dterm
                                           └──Type expr: Variable: 921
                                           └──Type expr: Variable: 922
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Constructor: dterm
                                        └──Type expr: Variable: 921
                                        └──Type expr: Variable: 922
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: 921
                                                 └──Type expr: Variable: 922
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: index
                                                          └──Type expr: Variable: 921
                                                          └──Type expr: Variable: 922
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: 921
                                                          └──Type expr: Variable: 922
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: 921
                                                       └──Type expr: Variable: 922
                                                    └──Desc: Variable: ix
                                           └──Expression:
                                              └──Type expr: Variable: 922
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: stack
                                                          └──Type expr: Variable: 921
                                                       └──Type expr: Variable: 922
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: 921
                                                                └──Type expr: Variable: 922
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: 921
                                                                └──Type expr: Variable: 922
                                                          └──Desc: Variable
                                                             └──Variable: prj
                                                             └──Type expr: Variable: 922
                                                             └──Type expr: Variable: 921
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: 921
                                                             └──Type expr: Variable: 922
                                                          └──Desc: Variable
                                                             └──Variable: ix
                                                 └──Expression:
                                                    └──Type expr: Constructor: stack
                                                       └──Type expr: Variable: 921
                                                    └──Desc: Variable
                                                       └──Variable: s
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: 921
                                                 └──Type expr: Variable: 922
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_con
                                                    └──Constructor argument type:
                                                       └──Type expr: Variable: 922
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: 921
                                                          └──Type expr: Variable: 922
                                                 └──Pattern:
                                                    └──Type expr: Variable: 922
                                                    └──Desc: Variable: v
                                           └──Expression:
                                              └──Type expr: Variable: 922
                                              └──Desc: Variable
                                                 └──Variable: v
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: 921
                                                 └──Type expr: Variable: 922
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_lam
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 921
                                                             └──Type expr: Variable: 979
                                                          └──Type expr: Variable: 977
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: 921
                                                          └──Type expr: Variable: 922
                                                 └──Pattern:
                                                    └──Type expr: Constructor: dterm
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 921
                                                          └──Type expr: Variable: 979
                                                       └──Type expr: Variable: 977
                                                    └──Desc: Variable: b
                                           └──Expression:
                                              └──Type expr: Variable: 922
                                              └──Desc: Function
                                                 └──Pattern:
                                                    └──Type expr: Variable: 979
                                                    └──Desc: Variable: x
                                                 └──Expression:
                                                    └──Type expr: Variable: 977
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 921
                                                                   └──Type expr: Variable: 979
                                                             └──Type expr: Variable: 977
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 921
                                                                         └──Type expr: Variable: 979
                                                                      └──Type expr: Variable: 977
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 921
                                                                            └──Type expr: Variable: 979
                                                                      └──Type expr: Variable: 977
                                                                └──Desc: Variable
                                                                   └──Variable: deval
                                                                   └──Type expr: Variable: 977
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 921
                                                                      └──Type expr: Variable: 979
                                                             └──Expression:
                                                                └──Type expr: Constructor: dterm
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 921
                                                                      └──Type expr: Variable: 979
                                                                   └──Type expr: Variable: 977
                                                                └──Desc: Variable
                                                                   └──Variable: b
                                                       └──Expression:
                                                          └──Type expr: Constructor: stack
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 921
                                                                └──Type expr: Variable: 979
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Push
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Variable: 921
                                                                      └──Type expr: Variable: 979
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: stack
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 921
                                                                         └──Type expr: Variable: 979
                                                             └──Expression:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: stack
                                                                      └──Type expr: Variable: 921
                                                                   └──Type expr: Variable: 979
                                                                └──Desc: Tuple
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Variable: 921
                                                                      └──Desc: Variable
                                                                         └──Variable: s
                                                                   └──Expression:
                                                                      └──Type expr: Variable: 979
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: 921
                                                 └──Type expr: Variable: 922
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_app
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: 921
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: 1042
                                                                └──Type expr: Variable: 922
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: 921
                                                             └──Type expr: Variable: 1042
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: 921
                                                          └──Type expr: Variable: 922
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: 921
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 1042
                                                             └──Type expr: Variable: 922
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: 921
                                                          └──Type expr: Variable: 1042
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: 921
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: 1042
                                                                └──Type expr: Variable: 922
                                                          └──Desc: Variable: f
                                                       └──Pattern:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: 921
                                                             └──Type expr: Variable: 1042
                                                          └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Variable: 922
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 1042
                                                       └──Type expr: Variable: 922
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: 921
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: 1042
                                                                └──Type expr: Variable: 922
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Variable: 921
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: 1042
                                                                         └──Type expr: Variable: 922
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Variable: 921
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: 1042
                                                                         └──Type expr: Variable: 922
                                                                └──Desc: Variable
                                                                   └──Variable: deval
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: 1042
                                                                      └──Type expr: Variable: 922
                                                                   └──Type expr: Variable: 921
                                                             └──Expression:
                                                                └──Type expr: Constructor: dterm
                                                                   └──Type expr: Variable: 921
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: 1042
                                                                      └──Type expr: Variable: 922
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Constructor: stack
                                                             └──Type expr: Variable: 921
                                                          └──Desc: Variable
                                                             └──Variable: s
                                                 └──Expression:
                                                    └──Type expr: Variable: 1042
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: 921
                                                             └──Type expr: Variable: 1042
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Variable: 921
                                                                      └──Type expr: Variable: 1042
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Variable: 921
                                                                      └──Type expr: Variable: 1042
                                                                └──Desc: Variable
                                                                   └──Variable: deval
                                                                   └──Type expr: Variable: 1042
                                                                   └──Type expr: Variable: 921
                                                             └──Expression:
                                                                └──Type expr: Constructor: dterm
                                                                   └──Type expr: Variable: 921
                                                                   └──Type expr: Variable: 1042
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: stack
                                                             └──Type expr: Variable: 921
                                                          └──Desc: Variable
                                                             └──Variable: s
       └──Structure item: Type
          └──Type declaration:
             └──Type name: layout
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Empty_layout
                   └──Constructor alphas: 2664 2665
                   └──Constructor type:
                      └──Type expr: Constructor: layout
                         └──Type expr: Variable: 2664
                         └──Type expr: Variable: 2665
                   └──Constraint:
                      └──Type expr: Variable: 2665
                      └──Type expr: Constructor: unit
                └──Constructor declaration:
                   └──Constructor name: Push_layout
                   └──Constructor alphas: 2664 2665
                   └──Constructor type:
                      └──Type expr: Constructor: layout
                         └──Type expr: Variable: 2664
                         └──Type expr: Variable: 2665
                   └──Constructor argument:
                      └──Constructor betas: 2669 2668
                      └──Type expr: Tuple
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 2668
                         └──Type expr: Constructor: layout
                            └──Type expr: Variable: 2664
                            └──Type expr: Variable: 2669
                         └──Type expr: Constructor: index
                            └──Type expr: Variable: 2664
                            └──Type expr: Variable: 2668
                   └──Constraint:
                      └──Type expr: Variable: 2665
                      └──Type expr: Tuple
                         └──Type expr: Variable: 2669
                         └──Type expr: Variable: 2668
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: size
                └──Abstraction:
                   └──Variables: 1096,1095
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: layout
                            └──Type expr: Variable: 1117
                            └──Type expr: Variable: 1118
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: layout
                               └──Type expr: Variable: 1117
                               └──Type expr: Variable: 1118
                            └──Desc: Variable: l
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: layout
                                     └──Type expr: Variable: 1117
                                     └──Type expr: Variable: 1118
                                  └──Desc: Variable
                                     └──Variable: l
                               └──Type expr: Constructor: layout
                                  └──Type expr: Variable: 1117
                                  └──Type expr: Variable: 1118
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: 1117
                                           └──Type expr: Variable: 1118
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Empty_layout
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: 1117
                                                    └──Type expr: Variable: 1118
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 0
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: 1117
                                           └──Type expr: Variable: 1118
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Push_layout
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 1153
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: 1117
                                                       └──Type expr: Variable: 1151
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: 1117
                                                       └──Type expr: Variable: 1153
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: 1117
                                                    └──Type expr: Variable: 1118
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 1153
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: 1117
                                                    └──Type expr: Variable: 1151
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: 1117
                                                    └──Type expr: Variable: 1153
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 1153
                                                    └──Desc: Any
                                                 └──Pattern:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: 1117
                                                       └──Type expr: Variable: 1151
                                                    └──Desc: Variable: l
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: 1117
                                                       └──Type expr: Variable: 1153
                                                    └──Desc: Any
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
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: 1117
                                                                └──Type expr: Variable: 1151
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: size
                                                             └──Type expr: Variable: 1151
                                                             └──Type expr: Variable: 1117
                                                       └──Expression:
                                                          └──Type expr: Constructor: layout
                                                             └──Type expr: Variable: 1117
                                                             └──Type expr: Variable: 1151
                                                          └──Desc: Variable
                                                             └──Variable: l
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 1
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: inc
                └──Abstraction:
                   └──Variables: 1202,1205,1204
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: layout
                            └──Type expr: Variable: 1232
                            └──Type expr: Variable: 1233
                         └──Type expr: Constructor: layout
                            └──Type expr: Tuple
                               └──Type expr: Variable: 1232
                               └──Type expr: Variable: 1264
                            └──Type expr: Variable: 1233
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: layout
                               └──Type expr: Variable: 1232
                               └──Type expr: Variable: 1233
                            └──Desc: Variable: l
                         └──Expression:
                            └──Type expr: Constructor: layout
                               └──Type expr: Tuple
                                  └──Type expr: Variable: 1232
                                  └──Type expr: Variable: 1264
                               └──Type expr: Variable: 1233
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: layout
                                     └──Type expr: Variable: 1232
                                     └──Type expr: Variable: 1233
                                  └──Desc: Variable
                                     └──Variable: l
                               └──Type expr: Constructor: layout
                                  └──Type expr: Variable: 1232
                                  └──Type expr: Variable: 1233
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: 1232
                                           └──Type expr: Variable: 1233
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Empty_layout
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: 1232
                                                    └──Type expr: Variable: 1233
                                     └──Expression:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 1232
                                              └──Type expr: Variable: 1264
                                           └──Type expr: Variable: 1233
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Empty_layout
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 1232
                                                       └──Type expr: Variable: 1264
                                                    └──Type expr: Variable: 1233
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: 1232
                                           └──Type expr: Variable: 1233
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Push_layout
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 1294
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: 1232
                                                       └──Type expr: Variable: 1292
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: 1232
                                                       └──Type expr: Variable: 1294
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: 1232
                                                    └──Type expr: Variable: 1233
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 1294
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: 1232
                                                    └──Type expr: Variable: 1292
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: 1232
                                                    └──Type expr: Variable: 1294
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 1294
                                                    └──Desc: Variable: t
                                                 └──Pattern:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: 1232
                                                       └──Type expr: Variable: 1292
                                                    └──Desc: Variable: l
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: 1232
                                                       └──Type expr: Variable: 1294
                                                    └──Desc: Variable: ix
                                     └──Expression:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 1232
                                              └──Type expr: Variable: 1264
                                           └──Type expr: Variable: 1233
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Push_layout
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 1294
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 1232
                                                          └──Type expr: Variable: 1264
                                                       └──Type expr: Variable: 1292
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 1232
                                                          └──Type expr: Variable: 1264
                                                       └──Type expr: Variable: 1294
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 1232
                                                       └──Type expr: Variable: 1264
                                                    └──Type expr: Variable: 1233
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 1294
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 1232
                                                       └──Type expr: Variable: 1264
                                                    └──Type expr: Variable: 1292
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 1232
                                                       └──Type expr: Variable: 1264
                                                    └──Type expr: Variable: 1294
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 1294
                                                    └──Desc: Variable
                                                       └──Variable: t
                                                 └──Expression:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 1232
                                                          └──Type expr: Variable: 1264
                                                       └──Type expr: Variable: 1292
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: 1232
                                                                └──Type expr: Variable: 1292
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 1232
                                                                   └──Type expr: Variable: 1264
                                                                └──Type expr: Variable: 1292
                                                          └──Desc: Variable
                                                             └──Variable: inc
                                                             └──Type expr: Variable: 1264
                                                             └──Type expr: Variable: 1292
                                                             └──Type expr: Variable: 1232
                                                       └──Expression:
                                                          └──Type expr: Constructor: layout
                                                             └──Type expr: Variable: 1232
                                                             └──Type expr: Variable: 1292
                                                          └──Desc: Variable
                                                             └──Variable: l
                                                 └──Expression:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 1232
                                                          └──Type expr: Variable: 1264
                                                       └──Type expr: Variable: 1294
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: 1232
                                                                └──Type expr: Variable: 1294
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 1232
                                                                   └──Type expr: Variable: 1264
                                                                └──Type expr: Variable: 1294
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: 1232
                                                             └──Type expr: Variable: 1294
                                                          └──Desc: Variable
                                                             └──Variable: ix
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: prjl
                └──Abstraction:
                   └──Variables: 1383,1382,1386
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 1418
                         └──Type expr: Arrow
                            └──Type expr: Constructor: int
                            └──Type expr: Arrow
                               └──Type expr: Constructor: layout
                                  └──Type expr: Variable: 1437
                                  └──Type expr: Variable: 1438
                               └──Type expr: Constructor: index
                                  └──Type expr: Variable: 1437
                                  └──Type expr: Variable: 1418
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: 1418
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: layout
                                     └──Type expr: Variable: 1437
                                     └──Type expr: Variable: 1438
                                  └──Type expr: Constructor: index
                                     └──Type expr: Variable: 1437
                                     └──Type expr: Variable: 1418
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable: n
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: layout
                                        └──Type expr: Variable: 1437
                                        └──Type expr: Variable: 1438
                                     └──Type expr: Constructor: index
                                        └──Type expr: Variable: 1437
                                        └──Type expr: Variable: 1418
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: 1437
                                           └──Type expr: Variable: 1438
                                        └──Desc: Variable: l
                                     └──Expression:
                                        └──Type expr: Constructor: index
                                           └──Type expr: Variable: 1437
                                           └──Type expr: Variable: 1418
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: layout
                                                 └──Type expr: Variable: 1437
                                                 └──Type expr: Variable: 1438
                                              └──Desc: Variable
                                                 └──Variable: l
                                           └──Type expr: Constructor: layout
                                              └──Type expr: Variable: 1437
                                              └──Type expr: Variable: 1438
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: 1437
                                                       └──Type expr: Variable: 1438
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Empty_layout
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: 1437
                                                                └──Type expr: Variable: 1438
                                                 └──Expression:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: 1437
                                                       └──Type expr: Variable: 1418
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: string
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: 1437
                                                                └──Type expr: Variable: 1418
                                                          └──Desc: Variable
                                                             └──Variable: fail_with
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: 1437
                                                                └──Type expr: Variable: 1418
                                                       └──Expression:
                                                          └──Type expr: Constructor: string
                                                          └──Desc: Constant: convert prjl
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: 1437
                                                       └──Type expr: Variable: 1438
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Push_layout
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 1487
                                                                └──Type expr: Constructor: layout
                                                                   └──Type expr: Variable: 1437
                                                                   └──Type expr: Variable: 1485
                                                                └──Type expr: Constructor: index
                                                                   └──Type expr: Variable: 1437
                                                                   └──Type expr: Variable: 1487
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: 1437
                                                                └──Type expr: Variable: 1438
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 1487
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: 1437
                                                                └──Type expr: Variable: 1485
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: 1437
                                                                └──Type expr: Variable: 1487
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 1487
                                                                └──Desc: Variable: t'
                                                             └──Pattern:
                                                                └──Type expr: Constructor: layout
                                                                   └──Type expr: Variable: 1437
                                                                   └──Type expr: Variable: 1485
                                                                └──Desc: Variable: l
                                                             └──Pattern:
                                                                └──Type expr: Constructor: index
                                                                   └──Type expr: Variable: 1437
                                                                   └──Type expr: Variable: 1487
                                                                └──Desc: Variable: ix
                                                 └──Expression:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: 1437
                                                       └──Type expr: Variable: 1418
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
                                                                         └──Variable: n
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Constant: 0
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: 1437
                                                             └──Type expr: Variable: 1418
                                                          └──Desc: Match
                                                             └──Expression:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: 1418
                                                                   └──Type expr: Variable: 1487
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: 1487
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: 1418
                                                                            └──Type expr: Variable: 1487
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: ty
                                                                                  └──Type expr: Variable: 1418
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: ty
                                                                                     └──Type expr: Variable: 1487
                                                                                  └──Type expr: Constructor: eq
                                                                                     └──Type expr: Variable: 1418
                                                                                     └──Type expr: Variable: 1487
                                                                            └──Desc: Variable
                                                                               └──Variable: check_eq
                                                                               └──Type expr: Variable: 1487
                                                                               └──Type expr: Variable: 1418
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: 1418
                                                                            └──Desc: Variable
                                                                               └──Variable: t
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: 1487
                                                                      └──Desc: Variable
                                                                         └──Variable: t'
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: 1418
                                                                └──Type expr: Variable: 1487
                                                             └──Cases:
                                                                └──Case:
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: eq
                                                                         └──Type expr: Variable: 1418
                                                                         └──Type expr: Variable: 1487
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Refl
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: eq
                                                                                  └──Type expr: Variable: 1418
                                                                                  └──Type expr: Variable: 1487
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: index
                                                                         └──Type expr: Variable: 1437
                                                                         └──Type expr: Variable: 1418
                                                                      └──Desc: Variable
                                                                         └──Variable: ix
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: 1437
                                                             └──Type expr: Variable: 1418
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: layout
                                                                      └──Type expr: Variable: 1437
                                                                      └──Type expr: Variable: 1485
                                                                   └──Type expr: Constructor: index
                                                                      └──Type expr: Variable: 1437
                                                                      └──Type expr: Variable: 1418
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: int
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: layout
                                                                               └──Type expr: Variable: 1437
                                                                               └──Type expr: Variable: 1485
                                                                            └──Type expr: Constructor: index
                                                                               └──Type expr: Variable: 1437
                                                                               └──Type expr: Variable: 1418
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: ty
                                                                                  └──Type expr: Variable: 1418
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: int
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: layout
                                                                                        └──Type expr: Variable: 1437
                                                                                        └──Type expr: Variable: 1485
                                                                                     └──Type expr: Constructor: index
                                                                                        └──Type expr: Variable: 1437
                                                                                        └──Type expr: Variable: 1418
                                                                            └──Desc: Variable
                                                                               └──Variable: prjl
                                                                               └──Type expr: Variable: 1485
                                                                               └──Type expr: Variable: 1437
                                                                               └──Type expr: Variable: 1418
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: 1418
                                                                            └──Desc: Variable
                                                                               └──Variable: t
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
                                                                                     └──Variable: n
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: int
                                                                            └──Desc: Constant: 1
                                                             └──Expression:
                                                                └──Type expr: Constructor: layout
                                                                   └──Type expr: Variable: 1437
                                                                   └──Type expr: Variable: 1485
                                                                └──Desc: Variable
                                                                   └──Variable: l
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: convert
                └──Abstraction:
                   └──Variables: 1612,1615
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: layout
                            └──Type expr: Variable: 1644
                            └──Type expr: Variable: 1644
                         └──Type expr: Arrow
                            └──Type expr: Constructor: hterm
                               └──Type expr: Variable: 1654
                            └──Type expr: Constructor: dterm
                               └──Type expr: Variable: 1644
                               └──Type expr: Variable: 1654
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: layout
                               └──Type expr: Variable: 1644
                               └──Type expr: Variable: 1644
                            └──Desc: Variable: l
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: hterm
                                  └──Type expr: Variable: 1654
                               └──Type expr: Constructor: dterm
                                  └──Type expr: Variable: 1644
                                  └──Type expr: Variable: 1654
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: hterm
                                     └──Type expr: Variable: 1654
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Constructor: dterm
                                     └──Type expr: Variable: 1644
                                     └──Type expr: Variable: 1654
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: 1654
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Constructor: hterm
                                        └──Type expr: Variable: 1654
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: hterm
                                                 └──Type expr: Variable: 1654
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Tag
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: 1654
                                                          └──Type expr: Constructor: int
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: 1654
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: 1654
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: 1654
                                                          └──Desc: Variable: t
                                                       └──Pattern:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable: sz
                                           └──Expression:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: 1644
                                                 └──Type expr: Variable: 1654
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: index
                                                          └──Type expr: Variable: 1644
                                                          └──Type expr: Variable: 1654
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: 1644
                                                          └──Type expr: Variable: 1654
                                                 └──Expression:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: 1644
                                                       └──Type expr: Variable: 1654
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: 1644
                                                                └──Type expr: Variable: 1644
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: 1644
                                                                └──Type expr: Variable: 1654
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: int
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Variable: 1644
                                                                         └──Type expr: Variable: 1644
                                                                      └──Type expr: Constructor: index
                                                                         └──Type expr: Variable: 1644
                                                                         └──Type expr: Variable: 1654
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: 1654
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: int
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: layout
                                                                                  └──Type expr: Variable: 1644
                                                                                  └──Type expr: Variable: 1644
                                                                               └──Type expr: Constructor: index
                                                                                  └──Type expr: Variable: 1644
                                                                                  └──Type expr: Variable: 1654
                                                                      └──Desc: Variable
                                                                         └──Variable: prjl
                                                                         └──Type expr: Variable: 1644
                                                                         └──Type expr: Variable: 1644
                                                                         └──Type expr: Variable: 1654
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: 1654
                                                                      └──Desc: Variable
                                                                         └──Variable: t
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
                                                                                        └──Desc: Primitive: (-)
                                                                                     └──Expression:
                                                                                        └──Type expr: Constructor: int
                                                                                        └──Desc: Application
                                                                                           └──Expression:
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Constructor: layout
                                                                                                    └──Type expr: Variable: 1644
                                                                                                    └──Type expr: Variable: 1644
                                                                                                 └──Type expr: Constructor: int
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: size
                                                                                                 └──Type expr: Variable: 1644
                                                                                                 └──Type expr: Variable: 1644
                                                                                           └──Expression:
                                                                                              └──Type expr: Constructor: layout
                                                                                                 └──Type expr: Variable: 1644
                                                                                                 └──Type expr: Variable: 1644
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: l
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: int
                                                                                  └──Desc: Variable
                                                                                     └──Variable: sz
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Constant: 1
                                                       └──Expression:
                                                          └──Type expr: Constructor: layout
                                                             └──Type expr: Variable: 1644
                                                             └──Type expr: Variable: 1644
                                                          └──Desc: Variable
                                                             └──Variable: l
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: hterm
                                                 └──Type expr: Variable: 1654
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Con
                                                    └──Constructor argument type:
                                                       └──Type expr: Variable: 1654
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: 1654
                                                 └──Pattern:
                                                    └──Type expr: Variable: 1654
                                                    └──Desc: Variable: v
                                           └──Expression:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: 1644
                                                 └──Type expr: Variable: 1654
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_con
                                                    └──Constructor argument type:
                                                       └──Type expr: Variable: 1654
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: 1644
                                                          └──Type expr: Variable: 1654
                                                 └──Expression:
                                                    └──Type expr: Variable: 1654
                                                    └──Desc: Variable
                                                       └──Variable: v
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: hterm
                                                 └──Type expr: Variable: 1654
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Lam
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: 1793
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: 1793
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: 1789
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: 1654
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: 1793
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: 1793
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: 1789
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: 1793
                                                          └──Desc: Variable: t
                                                       └──Pattern:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: 1793
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: 1789
                                                          └──Desc: Variable: f
                                           └──Expression:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: 1644
                                                 └──Type expr: Variable: 1654
                                              └──Desc: Let
                                                 └──Value bindings:
                                                    └──Value binding:
                                                       └──Pattern:
                                                          └──Type expr: Constructor: layout
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 1644
                                                                └──Type expr: Variable: 1793
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 1644
                                                                └──Type expr: Variable: 1793
                                                          └──Desc: Variable: l'
                                                       └──Abstraction:
                                                          └──Variables:
                                                          └──Expression:
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 1644
                                                                   └──Type expr: Variable: 1793
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 1644
                                                                   └──Type expr: Variable: 1793
                                                             └──Desc: Construct
                                                                └──Constructor description:
                                                                   └──Name: Push_layout
                                                                   └──Constructor argument type:
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: 1793
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 1644
                                                                               └──Type expr: Variable: 1793
                                                                            └──Type expr: Variable: 1644
                                                                         └──Type expr: Constructor: index
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 1644
                                                                               └──Type expr: Variable: 1793
                                                                            └──Type expr: Variable: 1793
                                                                   └──Constructor type:
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 1644
                                                                            └──Type expr: Variable: 1793
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 1644
                                                                            └──Type expr: Variable: 1793
                                                                └──Expression:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: 1793
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 1644
                                                                            └──Type expr: Variable: 1793
                                                                         └──Type expr: Variable: 1644
                                                                      └──Type expr: Constructor: index
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 1644
                                                                            └──Type expr: Variable: 1793
                                                                         └──Type expr: Variable: 1793
                                                                   └──Desc: Tuple
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: 1793
                                                                         └──Desc: Variable
                                                                            └──Variable: t
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 1644
                                                                               └──Type expr: Variable: 1793
                                                                            └──Type expr: Variable: 1644
                                                                         └──Desc: Application
                                                                            └──Expression:
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: layout
                                                                                     └──Type expr: Variable: 1644
                                                                                     └──Type expr: Variable: 1644
                                                                                  └──Type expr: Constructor: layout
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Variable: 1644
                                                                                        └──Type expr: Variable: 1793
                                                                                     └──Type expr: Variable: 1644
                                                                               └──Desc: Variable
                                                                                  └──Variable: inc
                                                                                  └──Type expr: Variable: 1793
                                                                                  └──Type expr: Variable: 1644
                                                                                  └──Type expr: Variable: 1644
                                                                            └──Expression:
                                                                               └──Type expr: Constructor: layout
                                                                                  └──Type expr: Variable: 1644
                                                                                  └──Type expr: Variable: 1644
                                                                               └──Desc: Variable
                                                                                  └──Variable: l
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: index
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 1644
                                                                               └──Type expr: Variable: 1793
                                                                            └──Type expr: Variable: 1793
                                                                         └──Desc: Construct
                                                                            └──Constructor description:
                                                                               └──Name: Zero
                                                                               └──Constructor argument type:
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Constructor type:
                                                                                  └──Type expr: Constructor: index
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Variable: 1644
                                                                                        └──Type expr: Variable: 1793
                                                                                     └──Type expr: Variable: 1793
                                                                            └──Expression:
                                                                               └──Type expr: Constructor: unit
                                                                               └──Desc: Constant: ()
                                                 └──Expression:
                                                    └──Type expr: Constructor: dterm
                                                       └──Type expr: Variable: 1644
                                                       └──Type expr: Variable: 1654
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: D_lam
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: dterm
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 1644
                                                                   └──Type expr: Variable: 1793
                                                                └──Type expr: Variable: 1789
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: dterm
                                                                └──Type expr: Variable: 1644
                                                                └──Type expr: Variable: 1654
                                                       └──Expression:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 1644
                                                                └──Type expr: Variable: 1793
                                                             └──Type expr: Variable: 1789
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: hterm
                                                                      └──Type expr: Variable: 1789
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 1644
                                                                         └──Type expr: Variable: 1793
                                                                      └──Type expr: Variable: 1789
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 1644
                                                                               └──Type expr: Variable: 1793
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 1644
                                                                               └──Type expr: Variable: 1793
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: hterm
                                                                               └──Type expr: Variable: 1789
                                                                            └──Type expr: Constructor: dterm
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: 1644
                                                                                  └──Type expr: Variable: 1793
                                                                               └──Type expr: Variable: 1789
                                                                      └──Desc: Variable
                                                                         └──Variable: convert
                                                                         └──Type expr: Variable: 1789
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 1644
                                                                            └──Type expr: Variable: 1793
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 1644
                                                                            └──Type expr: Variable: 1793
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 1644
                                                                            └──Type expr: Variable: 1793
                                                                      └──Desc: Variable
                                                                         └──Variable: l'
                                                             └──Expression:
                                                                └──Type expr: Constructor: hterm
                                                                   └──Type expr: Variable: 1789
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: hterm
                                                                            └──Type expr: Variable: 1793
                                                                         └──Type expr: Constructor: hterm
                                                                            └──Type expr: Variable: 1789
                                                                      └──Desc: Variable
                                                                         └──Variable: f
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: hterm
                                                                         └──Type expr: Variable: 1793
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Tag
                                                                            └──Constructor argument type:
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Constructor: ty
                                                                                     └──Type expr: Variable: 1793
                                                                                  └──Type expr: Constructor: int
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: hterm
                                                                                  └──Type expr: Variable: 1793
                                                                         └──Expression:
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Constructor: ty
                                                                                  └──Type expr: Variable: 1793
                                                                               └──Type expr: Constructor: int
                                                                            └──Desc: Tuple
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: ty
                                                                                     └──Type expr: Variable: 1793
                                                                                  └──Desc: Variable
                                                                                     └──Variable: t
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: int
                                                                                  └──Desc: Application
                                                                                     └──Expression:
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Constructor: layout
                                                                                              └──Type expr: Variable: 1644
                                                                                              └──Type expr: Variable: 1644
                                                                                           └──Type expr: Constructor: int
                                                                                        └──Desc: Variable
                                                                                           └──Variable: size
                                                                                           └──Type expr: Variable: 1644
                                                                                           └──Type expr: Variable: 1644
                                                                                     └──Expression:
                                                                                        └──Type expr: Constructor: layout
                                                                                           └──Type expr: Variable: 1644
                                                                                           └──Type expr: Variable: 1644
                                                                                        └──Desc: Variable
                                                                                           └──Variable: l
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: hterm
                                                 └──Type expr: Variable: 1654
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: App
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: 1931
                                                                └──Type expr: Variable: 1654
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: 1931
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: 1654
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 1931
                                                             └──Type expr: Variable: 1654
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: 1931
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: 1931
                                                                └──Type expr: Variable: 1654
                                                          └──Desc: Variable: f
                                                       └──Pattern:
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: 1931
                                                          └──Desc: Variable: a
                                           └──Expression:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: 1644
                                                 └──Type expr: Variable: 1654
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_app
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: 1644
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: 1931
                                                                └──Type expr: Variable: 1654
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: 1644
                                                             └──Type expr: Variable: 1931
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: 1644
                                                          └──Type expr: Variable: 1654
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: 1644
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 1931
                                                             └──Type expr: Variable: 1654
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: 1644
                                                          └──Type expr: Variable: 1931
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: 1644
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: 1931
                                                                └──Type expr: Variable: 1654
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: hterm
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: 1931
                                                                         └──Type expr: Variable: 1654
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Variable: 1644
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: 1931
                                                                         └──Type expr: Variable: 1654
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Variable: 1644
                                                                            └──Type expr: Variable: 1644
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: hterm
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: 1931
                                                                                  └──Type expr: Variable: 1654
                                                                            └──Type expr: Constructor: dterm
                                                                               └──Type expr: Variable: 1644
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: 1931
                                                                                  └──Type expr: Variable: 1654
                                                                      └──Desc: Variable
                                                                         └──Variable: convert
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Variable: 1931
                                                                            └──Type expr: Variable: 1654
                                                                         └──Type expr: Variable: 1644
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Variable: 1644
                                                                         └──Type expr: Variable: 1644
                                                                      └──Desc: Variable
                                                                         └──Variable: l
                                                             └──Expression:
                                                                └──Type expr: Constructor: hterm
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: 1931
                                                                      └──Type expr: Variable: 1654
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: 1644
                                                             └──Type expr: Variable: 1931
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: hterm
                                                                      └──Type expr: Variable: 1931
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Variable: 1644
                                                                      └──Type expr: Variable: 1931
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Variable: 1644
                                                                            └──Type expr: Variable: 1644
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: hterm
                                                                               └──Type expr: Variable: 1931
                                                                            └──Type expr: Constructor: dterm
                                                                               └──Type expr: Variable: 1644
                                                                               └──Type expr: Variable: 1931
                                                                      └──Desc: Variable
                                                                         └──Variable: convert
                                                                         └──Type expr: Variable: 1931
                                                                         └──Type expr: Variable: 1644
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Variable: 1644
                                                                         └──Type expr: Variable: 1644
                                                                      └──Desc: Variable
                                                                         └──Variable: l
                                                             └──Expression:
                                                                └──Type expr: Constructor: hterm
                                                                   └──Type expr: Variable: 1931
                                                                └──Desc: Variable
                                                                   └──Variable: a |}]