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
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: int
                └──Constructor declaration:
                   └──Constructor name: String
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: string
                └──Constructor declaration:
                   └──Constructor name: List
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas: b
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: b
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: b
                └──Constructor declaration:
                   └──Constructor name: Pair
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas: b c
                      └──Type expr: Tuple
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: b
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: c
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Tuple
                         └──Type expr: Variable: b
                         └──Type expr: Variable: c
                └──Constructor declaration:
                   └──Constructor name: Fun
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas: b c
                      └──Type expr: Tuple
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: b
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: c
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Arrow
                         └──Type expr: Variable: b
                         └──Type expr: Variable: c
       └──Structure item: Type
          └──Type declaration:
             └──Type name: eq
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Refl
                   └──Constructor alphas: a b
                   └──Constructor type:
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Variable: b
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
                   └──Variables: a2589,a2591
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: a2617
                         └──Type expr: Arrow
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: a2627
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: a2617
                               └──Type expr: Variable: a2627
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: a2617
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: ty
                                  └──Type expr: Variable: a2627
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: a2617
                                  └──Type expr: Variable: a2627
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: ty
                                     └──Type expr: Variable: a2627
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: a2617
                                     └──Type expr: Variable: a2627
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: ty
                                              └──Type expr: Variable: a2617
                                           └──Type expr: Constructor: ty
                                              └──Type expr: Variable: a2627
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: a2617
                                              └──Desc: Variable
                                                 └──Variable: t1
                                           └──Expression:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: a2627
                                              └──Desc: Variable
                                                 └──Variable: t2
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: ty
                                           └──Type expr: Variable: a2617
                                        └──Type expr: Constructor: ty
                                           └──Type expr: Variable: a2627
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a2617
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a2627
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a2617
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a2617
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a2627
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a2627
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a2617
                                                 └──Type expr: Variable: a2627
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Refl
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a2617
                                                          └──Type expr: Variable: a2617
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a2617
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a2627
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a2617
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: String
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a2617
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a2627
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: String
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a2627
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a2617
                                                 └──Type expr: Variable: a2627
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Refl
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a2617
                                                          └──Type expr: Variable: a2617
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a2617
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a2627
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a2617
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: List
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a2709
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a2617
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a2709
                                                          └──Desc: Variable: t1
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a2627
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: List
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a2706
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a2627
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a2706
                                                          └──Desc: Variable: t2
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a2617
                                                 └──Type expr: Variable: a2627
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a2709
                                                       └──Type expr: Variable: a2706
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a2706
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a2709
                                                                └──Type expr: Variable: a2706
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: a2709
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a2706
                                                                      └──Type expr: Constructor: eq
                                                                         └──Type expr: Variable: a2709
                                                                         └──Type expr: Variable: a2706
                                                                └──Desc: Variable
                                                                   └──Variable: check_eq
                                                                   └──Type expr: Variable: a2706
                                                                   └──Type expr: Variable: a2709
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a2709
                                                                └──Desc: Variable
                                                                   └──Variable: t1
                                                       └──Expression:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a2706
                                                          └──Desc: Variable
                                                             └──Variable: t2
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: a2709
                                                    └──Type expr: Variable: a2706
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a2709
                                                             └──Type expr: Variable: a2706
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Refl
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a2709
                                                                      └──Type expr: Variable: a2706
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a2617
                                                             └──Type expr: Variable: a2627
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Refl
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a2617
                                                                      └──Type expr: Variable: a2617
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a2617
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a2627
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a2617
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Pair
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a2791
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a2789
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a2617
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a2791
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a2789
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a2791
                                                                └──Desc: Variable: t11
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a2789
                                                                └──Desc: Variable: t12
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a2627
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Pair
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a2785
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a2783
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a2627
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a2785
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a2783
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a2785
                                                                └──Desc: Variable: t21
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a2783
                                                                └──Desc: Variable: t22
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a2617
                                                 └──Type expr: Variable: a2627
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a2791
                                                          └──Type expr: Variable: a2785
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a2789
                                                          └──Type expr: Variable: a2783
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a2791
                                                             └──Type expr: Variable: a2785
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: a2785
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a2791
                                                                      └──Type expr: Variable: a2785
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a2791
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: a2785
                                                                            └──Type expr: Constructor: eq
                                                                               └──Type expr: Variable: a2791
                                                                               └──Type expr: Variable: a2785
                                                                      └──Desc: Variable
                                                                         └──Variable: check_eq
                                                                         └──Type expr: Variable: a2785
                                                                         └──Type expr: Variable: a2791
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a2791
                                                                      └──Desc: Variable
                                                                         └──Variable: t11
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a2785
                                                                └──Desc: Variable
                                                                   └──Variable: t21
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a2789
                                                             └──Type expr: Variable: a2783
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: a2783
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a2789
                                                                      └──Type expr: Variable: a2783
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a2789
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: a2783
                                                                            └──Type expr: Constructor: eq
                                                                               └──Type expr: Variable: a2789
                                                                               └──Type expr: Variable: a2783
                                                                      └──Desc: Variable
                                                                         └──Variable: check_eq
                                                                         └──Type expr: Variable: a2783
                                                                         └──Type expr: Variable: a2789
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a2789
                                                                      └──Desc: Variable
                                                                         └──Variable: t12
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a2783
                                                                └──Desc: Variable
                                                                   └──Variable: t22
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a2791
                                                       └──Type expr: Variable: a2785
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a2789
                                                       └──Type expr: Variable: a2783
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a2791
                                                                └──Type expr: Variable: a2785
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a2789
                                                                └──Type expr: Variable: a2783
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: a2791
                                                                   └──Type expr: Variable: a2785
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: a2791
                                                                            └──Type expr: Variable: a2785
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: a2789
                                                                   └──Type expr: Variable: a2783
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: a2789
                                                                            └──Type expr: Variable: a2783
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a2617
                                                             └──Type expr: Variable: a2627
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Refl
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a2617
                                                                      └──Type expr: Variable: a2617
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a2617
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a2627
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a2617
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fun
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a2912
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a2910
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a2617
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a2912
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a2910
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a2912
                                                                └──Desc: Variable: t11
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a2910
                                                                └──Desc: Variable: t12
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a2627
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fun
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a2906
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a2904
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a2627
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a2906
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a2904
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a2906
                                                                └──Desc: Variable: t21
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a2904
                                                                └──Desc: Variable: t22
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a2617
                                                 └──Type expr: Variable: a2627
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a2912
                                                          └──Type expr: Variable: a2906
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a2910
                                                          └──Type expr: Variable: a2904
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a2912
                                                             └──Type expr: Variable: a2906
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: a2906
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a2912
                                                                      └──Type expr: Variable: a2906
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a2912
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: a2906
                                                                            └──Type expr: Constructor: eq
                                                                               └──Type expr: Variable: a2912
                                                                               └──Type expr: Variable: a2906
                                                                      └──Desc: Variable
                                                                         └──Variable: check_eq
                                                                         └──Type expr: Variable: a2906
                                                                         └──Type expr: Variable: a2912
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a2912
                                                                      └──Desc: Variable
                                                                         └──Variable: t11
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a2906
                                                                └──Desc: Variable
                                                                   └──Variable: t21
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a2910
                                                             └──Type expr: Variable: a2904
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: a2904
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a2910
                                                                      └──Type expr: Variable: a2904
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a2910
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: a2904
                                                                            └──Type expr: Constructor: eq
                                                                               └──Type expr: Variable: a2910
                                                                               └──Type expr: Variable: a2904
                                                                      └──Desc: Variable
                                                                         └──Variable: check_eq
                                                                         └──Type expr: Variable: a2904
                                                                         └──Type expr: Variable: a2910
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a2910
                                                                      └──Desc: Variable
                                                                         └──Variable: t12
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a2904
                                                                └──Desc: Variable
                                                                   └──Variable: t22
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a2912
                                                       └──Type expr: Variable: a2906
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a2910
                                                       └──Type expr: Variable: a2904
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a2912
                                                                └──Type expr: Variable: a2906
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a2910
                                                                └──Type expr: Variable: a2904
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: a2912
                                                                   └──Type expr: Variable: a2906
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: a2912
                                                                            └──Type expr: Variable: a2906
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: a2910
                                                                   └──Type expr: Variable: a2904
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: a2910
                                                                            └──Type expr: Variable: a2904
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a2617
                                                             └──Type expr: Variable: a2627
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Refl
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a2617
                                                                      └──Type expr: Variable: a2617
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: a3019
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: a3029
                         └──Type expr: Arrow
                            └──Type expr: Variable: a3019
                            └──Type expr: Variable: a3029
                   └──Desc: Variable: cast
                └──Abstraction:
                   └──Variables: a3019,a3029
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: a3019
                         └──Type expr: Arrow
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: a3029
                            └──Type expr: Arrow
                               └──Type expr: Variable: a3019
                               └──Type expr: Variable: a3029
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: a3019
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: ty
                                  └──Type expr: Variable: a3029
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a3019
                                  └──Type expr: Variable: a3029
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: ty
                                     └──Type expr: Variable: a3029
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a3019
                                     └──Type expr: Variable: a3029
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: a3019
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: a3029
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a3019
                                                 └──Type expr: Variable: a3029
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: a3029
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a3019
                                                          └──Type expr: Variable: a3029
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a3019
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a3029
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: a3019
                                                                   └──Type expr: Variable: a3029
                                                          └──Desc: Variable
                                                             └──Variable: check_eq
                                                             └──Type expr: Variable: a3029
                                                             └──Type expr: Variable: a3019
                                                       └──Expression:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a3019
                                                          └──Desc: Variable
                                                             └──Variable: t1
                                                 └──Expression:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a3029
                                                    └──Desc: Variable
                                                       └──Variable: t2
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: a3019
                                              └──Type expr: Variable: a3029
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a3019
                                                       └──Type expr: Variable: a3029
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Refl
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a3019
                                                                └──Type expr: Variable: a3029
                                                 └──Expression:
                                                    └──Type expr: Variable: a3029
                                                    └──Desc: Variable
                                                       └──Variable: x
       └──Structure item: Type
          └──Type declaration:
             └──Type name: hterm
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Tag
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: hterm
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: a
                         └──Type expr: Constructor: int
                └──Constructor declaration:
                   └──Constructor name: Con
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: hterm
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: a
                └──Constructor declaration:
                   └──Constructor name: Lam
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: hterm
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas: b c
                      └──Type expr: Tuple
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: b
                         └──Type expr: Arrow
                            └──Type expr: Constructor: hterm
                               └──Type expr: Variable: b
                            └──Type expr: Constructor: hterm
                               └──Type expr: Variable: c
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Arrow
                         └──Type expr: Variable: b
                         └──Type expr: Variable: c
                └──Constructor declaration:
                   └──Constructor name: App
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: hterm
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas: b
                      └──Type expr: Tuple
                         └──Type expr: Constructor: hterm
                            └──Type expr: Arrow
                               └──Type expr: Variable: b
                               └──Type expr: Variable: a
                         └──Type expr: Constructor: hterm
                            └──Type expr: Variable: b
       └──Structure item: Primitive
          └──Value description:
             └──Name: fail_with
             └──Scheme:
                └──Variables: a3069
                └──Type expr: Arrow
                   └──Type expr: Constructor: string
                   └──Type expr: Variable: a3069
             └──Primitive name: %fail_with
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: heval
                └──Abstraction:
                   └──Variables: a3078
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: hterm
                            └──Type expr: Variable: a3095
                         └──Type expr: Variable: a3095
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: hterm
                               └──Type expr: Variable: a3095
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Variable: a3095
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: hterm
                                     └──Type expr: Variable: a3095
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: hterm
                                  └──Type expr: Variable: a3095
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: a3095
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Tag
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a3095
                                                    └──Type expr: Constructor: int
                                              └──Constructor type:
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: a3095
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a3095
                                                 └──Type expr: Constructor: int
                                              └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Variable: a3095
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: string
                                                 └──Type expr: Variable: a3095
                                              └──Desc: Variable
                                                 └──Variable: fail_with
                                                 └──Type expr: Variable: a3095
                                           └──Expression:
                                              └──Type expr: Constructor: string
                                              └──Desc: Constant: HOAS eval
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: a3095
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Con
                                              └──Constructor argument type:
                                                 └──Type expr: Variable: a3095
                                              └──Constructor type:
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: a3095
                                           └──Pattern:
                                              └──Type expr: Variable: a3095
                                              └──Desc: Variable: v
                                     └──Expression:
                                        └──Type expr: Variable: a3095
                                        └──Desc: Variable
                                           └──Variable: v
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: a3095
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Lam
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a3144
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a3144
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a3140
                                              └──Constructor type:
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: a3095
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a3144
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: a3144
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: a3140
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a3144
                                                    └──Desc: Any
                                                 └──Pattern:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a3144
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a3140
                                                    └──Desc: Variable: f
                                     └──Expression:
                                        └──Type expr: Variable: a3095
                                        └──Desc: Function
                                           └──Pattern:
                                              └──Type expr: Variable: a3144
                                              └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Variable: a3140
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a3140
                                                       └──Type expr: Variable: a3140
                                                    └──Desc: Variable
                                                       └──Variable: heval
                                                       └──Type expr: Variable: a3140
                                                 └──Expression:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: a3140
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: a3144
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: a3140
                                                          └──Desc: Variable
                                                             └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: a3144
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Con
                                                                └──Constructor argument type:
                                                                   └──Type expr: Variable: a3144
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: hterm
                                                                      └──Type expr: Variable: a3144
                                                             └──Expression:
                                                                └──Type expr: Variable: a3144
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: a3095
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: App
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: a3192
                                                          └──Type expr: Variable: a3095
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: a3192
                                              └──Constructor type:
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: a3095
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: a3192
                                                       └──Type expr: Variable: a3095
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: a3192
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: a3192
                                                          └──Type expr: Variable: a3095
                                                    └──Desc: Variable: f
                                                 └──Pattern:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: a3192
                                                    └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: a3095
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: a3192
                                                 └──Type expr: Variable: a3095
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a3192
                                                             └──Type expr: Variable: a3095
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: a3192
                                                          └──Type expr: Variable: a3095
                                                    └──Desc: Variable
                                                       └──Variable: heval
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: a3192
                                                          └──Type expr: Variable: a3095
                                                 └──Expression:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: a3192
                                                          └──Type expr: Variable: a3095
                                                    └──Desc: Variable
                                                       └──Variable: f
                                           └──Expression:
                                              └──Type expr: Variable: a3192
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a3192
                                                       └──Type expr: Variable: a3192
                                                    └──Desc: Variable
                                                       └──Variable: heval
                                                       └──Type expr: Variable: a3192
                                                 └──Expression:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: a3192
                                                    └──Desc: Variable
                                                       └──Variable: x
       └──Structure item: Type
          └──Type declaration:
             └──Type name: index
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Zero
                   └──Constructor alphas: env t
                   └──Constructor type:
                      └──Type expr: Constructor: index
                         └──Type expr: Variable: env
                         └──Type expr: Variable: t
                   └──Constructor argument:
                      └──Constructor betas: env1
                      └──Type expr: Constructor: unit
                   └──Constraint:
                      └──Type expr: Variable: env
                      └──Type expr: Tuple
                         └──Type expr: Variable: env1
                         └──Type expr: Variable: t
                └──Constructor declaration:
                   └──Constructor name: Succ
                   └──Constructor alphas: env t
                   └──Constructor type:
                      └──Type expr: Constructor: index
                         └──Type expr: Variable: env
                         └──Type expr: Variable: t
                   └──Constructor argument:
                      └──Constructor betas: env1 s
                      └──Type expr: Constructor: index
                         └──Type expr: Variable: env1
                         └──Type expr: Variable: t
                   └──Constraint:
                      └──Type expr: Variable: env
                      └──Type expr: Tuple
                         └──Type expr: Variable: env1
                         └──Type expr: Variable: s
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: index_to_int
                └──Abstraction:
                   └──Variables: a3229,a3228
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: index
                            └──Type expr: Variable: a3250
                            └──Type expr: Variable: a3251
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: index
                               └──Type expr: Variable: a3250
                               └──Type expr: Variable: a3251
                            └──Desc: Variable: ix
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: index
                                     └──Type expr: Variable: a3250
                                     └──Type expr: Variable: a3251
                                  └──Desc: Variable
                                     └──Variable: ix
                               └──Type expr: Constructor: index
                                  └──Type expr: Variable: a3250
                                  └──Type expr: Variable: a3251
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: index
                                           └──Type expr: Variable: a3250
                                           └──Type expr: Variable: a3251
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Zero
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: a3250
                                                    └──Type expr: Variable: a3251
                                           └──Pattern:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 0
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: index
                                           └──Type expr: Variable: a3250
                                           └──Type expr: Variable: a3251
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: a3280
                                                    └──Type expr: Variable: a3251
                                              └──Constructor type:
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: a3250
                                                    └──Type expr: Variable: a3251
                                           └──Pattern:
                                              └──Type expr: Constructor: index
                                                 └──Type expr: Variable: a3280
                                                 └──Type expr: Variable: a3251
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
                                                                └──Type expr: Variable: a3280
                                                                └──Type expr: Variable: a3251
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: index_to_int
                                                             └──Type expr: Variable: a3251
                                                             └──Type expr: Variable: a3280
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: a3280
                                                             └──Type expr: Variable: a3251
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
                   └──Constructor alphas: env
                   └──Constructor type:
                      └──Type expr: Constructor: stack
                         └──Type expr: Variable: env
                   └──Constraint:
                      └──Type expr: Variable: env
                      └──Type expr: Constructor: unit
                └──Constructor declaration:
                   └──Constructor name: Push
                   └──Constructor alphas: env
                   └──Constructor type:
                      └──Type expr: Constructor: stack
                         └──Type expr: Variable: env
                   └──Constructor argument:
                      └──Constructor betas: env1 t
                      └──Type expr: Tuple
                         └──Type expr: Constructor: stack
                            └──Type expr: Variable: env1
                         └──Type expr: Variable: t
                   └──Constraint:
                      └──Type expr: Variable: env
                      └──Type expr: Tuple
                         └──Type expr: Variable: env1
                         └──Type expr: Variable: t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: prj
                └──Abstraction:
                   └──Variables: a3329,a3328
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: index
                            └──Type expr: Variable: a3354
                            └──Type expr: Variable: a3355
                         └──Type expr: Arrow
                            └──Type expr: Constructor: stack
                               └──Type expr: Variable: a3354
                            └──Type expr: Variable: a3355
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: index
                               └──Type expr: Variable: a3354
                               └──Type expr: Variable: a3355
                            └──Desc: Variable: ix
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: stack
                                  └──Type expr: Variable: a3354
                               └──Type expr: Variable: a3355
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: stack
                                     └──Type expr: Variable: a3354
                                  └──Desc: Variable: s
                               └──Expression:
                                  └──Type expr: Variable: a3355
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: index
                                              └──Type expr: Variable: a3354
                                              └──Type expr: Variable: a3355
                                           └──Type expr: Constructor: stack
                                              └──Type expr: Variable: a3354
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: index
                                                 └──Type expr: Variable: a3354
                                                 └──Type expr: Variable: a3355
                                              └──Desc: Variable
                                                 └──Variable: ix
                                           └──Expression:
                                              └──Type expr: Constructor: stack
                                                 └──Type expr: Variable: a3354
                                              └──Desc: Variable
                                                 └──Variable: s
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: index
                                           └──Type expr: Variable: a3354
                                           └──Type expr: Variable: a3355
                                        └──Type expr: Constructor: stack
                                           └──Type expr: Variable: a3354
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: a3354
                                                    └──Type expr: Variable: a3355
                                                 └──Type expr: Constructor: stack
                                                    └──Type expr: Variable: a3354
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a3354
                                                       └──Type expr: Variable: a3355
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a3354
                                                                └──Type expr: Variable: a3355
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                                 └──Pattern:
                                                    └──Type expr: Constructor: stack
                                                       └──Type expr: Variable: a3354
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Push
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: a3392
                                                                └──Type expr: Variable: a3390
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: a3354
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: a3392
                                                             └──Type expr: Variable: a3390
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: a3392
                                                                └──Desc: Any
                                                             └──Pattern:
                                                                └──Type expr: Variable: a3390
                                                                └──Desc: Variable: v
                                           └──Expression:
                                              └──Type expr: Variable: a3355
                                              └──Desc: Variable
                                                 └──Variable: v
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: a3354
                                                    └──Type expr: Variable: a3355
                                                 └──Type expr: Constructor: stack
                                                    └──Type expr: Variable: a3354
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a3354
                                                       └──Type expr: Variable: a3355
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a3430
                                                                └──Type expr: Variable: a3355
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a3354
                                                                └──Type expr: Variable: a3355
                                                       └──Pattern:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: a3430
                                                             └──Type expr: Variable: a3355
                                                          └──Desc: Variable: ix
                                                 └──Pattern:
                                                    └──Type expr: Constructor: stack
                                                       └──Type expr: Variable: a3354
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Push
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: a3427
                                                                └──Type expr: Variable: a3425
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: a3354
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: a3427
                                                             └──Type expr: Variable: a3425
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: a3427
                                                                └──Desc: Variable: s
                                                             └──Pattern:
                                                                └──Type expr: Variable: a3425
                                                                └──Desc: Any
                                           └──Expression:
                                              └──Type expr: Variable: a3355
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: stack
                                                          └──Type expr: Variable: a3427
                                                       └──Type expr: Variable: a3355
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a3427
                                                                └──Type expr: Variable: a3355
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: a3427
                                                                └──Type expr: Variable: a3355
                                                          └──Desc: Variable
                                                             └──Variable: prj
                                                             └──Type expr: Variable: a3355
                                                             └──Type expr: Variable: a3427
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: a3427
                                                             └──Type expr: Variable: a3355
                                                          └──Desc: Variable
                                                             └──Variable: ix
                                                 └──Expression:
                                                    └──Type expr: Constructor: stack
                                                       └──Type expr: Variable: a3427
                                                    └──Desc: Variable
                                                       └──Variable: s
       └──Structure item: Type
          └──Type declaration:
             └──Type name: dterm
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: D_var
                   └──Constructor alphas: env t
                   └──Constructor type:
                      └──Type expr: Constructor: dterm
                         └──Type expr: Variable: env
                         └──Type expr: Variable: t
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: index
                         └──Type expr: Variable: env
                         └──Type expr: Variable: t
                └──Constructor declaration:
                   └──Constructor name: D_con
                   └──Constructor alphas: env t
                   └──Constructor type:
                      └──Type expr: Constructor: dterm
                         └──Type expr: Variable: env
                         └──Type expr: Variable: t
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: t
                └──Constructor declaration:
                   └──Constructor name: D_lam
                   └──Constructor alphas: env t
                   └──Constructor type:
                      └──Type expr: Constructor: dterm
                         └──Type expr: Variable: env
                         └──Type expr: Variable: t
                   └──Constructor argument:
                      └──Constructor betas: s r
                      └──Type expr: Constructor: dterm
                         └──Type expr: Tuple
                            └──Type expr: Variable: env
                            └──Type expr: Variable: s
                         └──Type expr: Variable: r
                   └──Constraint:
                      └──Type expr: Variable: t
                      └──Type expr: Arrow
                         └──Type expr: Variable: s
                         └──Type expr: Variable: r
                └──Constructor declaration:
                   └──Constructor name: D_app
                   └──Constructor alphas: env t
                   └──Constructor type:
                      └──Type expr: Constructor: dterm
                         └──Type expr: Variable: env
                         └──Type expr: Variable: t
                   └──Constructor argument:
                      └──Constructor betas: s
                      └──Type expr: Tuple
                         └──Type expr: Constructor: dterm
                            └──Type expr: Variable: env
                            └──Type expr: Arrow
                               └──Type expr: Variable: s
                               └──Type expr: Variable: t
                         └──Type expr: Constructor: dterm
                            └──Type expr: Variable: env
                            └──Type expr: Variable: s
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: deval
                └──Abstraction:
                   └──Variables: a3475,a3474
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: dterm
                            └──Type expr: Variable: a3500
                            └──Type expr: Variable: a3501
                         └──Type expr: Arrow
                            └──Type expr: Constructor: stack
                               └──Type expr: Variable: a3500
                            └──Type expr: Variable: a3501
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: dterm
                               └──Type expr: Variable: a3500
                               └──Type expr: Variable: a3501
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: stack
                                  └──Type expr: Variable: a3500
                               └──Type expr: Variable: a3501
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: stack
                                     └──Type expr: Variable: a3500
                                  └──Desc: Variable: s
                               └──Expression:
                                  └──Type expr: Variable: a3501
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: dterm
                                           └──Type expr: Variable: a3500
                                           └──Type expr: Variable: a3501
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Constructor: dterm
                                        └──Type expr: Variable: a3500
                                        └──Type expr: Variable: a3501
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a3500
                                                 └──Type expr: Variable: a3501
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: index
                                                          └──Type expr: Variable: a3500
                                                          └──Type expr: Variable: a3501
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a3500
                                                          └──Type expr: Variable: a3501
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a3500
                                                       └──Type expr: Variable: a3501
                                                    └──Desc: Variable: ix
                                           └──Expression:
                                              └──Type expr: Variable: a3501
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: stack
                                                          └──Type expr: Variable: a3500
                                                       └──Type expr: Variable: a3501
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a3500
                                                                └──Type expr: Variable: a3501
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: a3500
                                                                └──Type expr: Variable: a3501
                                                          └──Desc: Variable
                                                             └──Variable: prj
                                                             └──Type expr: Variable: a3501
                                                             └──Type expr: Variable: a3500
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: a3500
                                                             └──Type expr: Variable: a3501
                                                          └──Desc: Variable
                                                             └──Variable: ix
                                                 └──Expression:
                                                    └──Type expr: Constructor: stack
                                                       └──Type expr: Variable: a3500
                                                    └──Desc: Variable
                                                       └──Variable: s
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a3500
                                                 └──Type expr: Variable: a3501
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_con
                                                    └──Constructor argument type:
                                                       └──Type expr: Variable: a3501
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a3500
                                                          └──Type expr: Variable: a3501
                                                 └──Pattern:
                                                    └──Type expr: Variable: a3501
                                                    └──Desc: Variable: v
                                           └──Expression:
                                              └──Type expr: Variable: a3501
                                              └──Desc: Variable
                                                 └──Variable: v
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a3500
                                                 └──Type expr: Variable: a3501
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_lam
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a3500
                                                             └──Type expr: Variable: a3558
                                                          └──Type expr: Variable: a3556
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a3500
                                                          └──Type expr: Variable: a3501
                                                 └──Pattern:
                                                    └──Type expr: Constructor: dterm
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a3500
                                                          └──Type expr: Variable: a3558
                                                       └──Type expr: Variable: a3556
                                                    └──Desc: Variable: b
                                           └──Expression:
                                              └──Type expr: Variable: a3501
                                              └──Desc: Function
                                                 └──Pattern:
                                                    └──Type expr: Variable: a3558
                                                    └──Desc: Variable: x
                                                 └──Expression:
                                                    └──Type expr: Variable: a3556
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a3500
                                                                   └──Type expr: Variable: a3558
                                                             └──Type expr: Variable: a3556
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a3500
                                                                         └──Type expr: Variable: a3558
                                                                      └──Type expr: Variable: a3556
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a3500
                                                                            └──Type expr: Variable: a3558
                                                                      └──Type expr: Variable: a3556
                                                                └──Desc: Variable
                                                                   └──Variable: deval
                                                                   └──Type expr: Variable: a3556
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a3500
                                                                      └──Type expr: Variable: a3558
                                                             └──Expression:
                                                                └──Type expr: Constructor: dterm
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a3500
                                                                      └──Type expr: Variable: a3558
                                                                   └──Type expr: Variable: a3556
                                                                └──Desc: Variable
                                                                   └──Variable: b
                                                       └──Expression:
                                                          └──Type expr: Constructor: stack
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a3500
                                                                └──Type expr: Variable: a3558
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Push
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Variable: a3500
                                                                      └──Type expr: Variable: a3558
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: stack
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a3500
                                                                         └──Type expr: Variable: a3558
                                                             └──Expression:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: stack
                                                                      └──Type expr: Variable: a3500
                                                                   └──Type expr: Variable: a3558
                                                                └──Desc: Tuple
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Variable: a3500
                                                                      └──Desc: Variable
                                                                         └──Variable: s
                                                                   └──Expression:
                                                                      └──Type expr: Variable: a3558
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a3500
                                                 └──Type expr: Variable: a3501
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_app
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a3500
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a3621
                                                                └──Type expr: Variable: a3501
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a3500
                                                             └──Type expr: Variable: a3621
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a3500
                                                          └──Type expr: Variable: a3501
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a3500
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a3621
                                                             └──Type expr: Variable: a3501
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a3500
                                                          └──Type expr: Variable: a3621
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a3500
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a3621
                                                                └──Type expr: Variable: a3501
                                                          └──Desc: Variable: f
                                                       └──Pattern:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a3500
                                                             └──Type expr: Variable: a3621
                                                          └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Variable: a3501
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: a3621
                                                       └──Type expr: Variable: a3501
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: a3500
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a3621
                                                                └──Type expr: Variable: a3501
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Variable: a3500
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: a3621
                                                                         └──Type expr: Variable: a3501
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Variable: a3500
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: a3621
                                                                         └──Type expr: Variable: a3501
                                                                └──Desc: Variable
                                                                   └──Variable: deval
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a3621
                                                                      └──Type expr: Variable: a3501
                                                                   └──Type expr: Variable: a3500
                                                             └──Expression:
                                                                └──Type expr: Constructor: dterm
                                                                   └──Type expr: Variable: a3500
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a3621
                                                                      └──Type expr: Variable: a3501
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Constructor: stack
                                                             └──Type expr: Variable: a3500
                                                          └──Desc: Variable
                                                             └──Variable: s
                                                 └──Expression:
                                                    └──Type expr: Variable: a3621
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: a3500
                                                             └──Type expr: Variable: a3621
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Variable: a3500
                                                                      └──Type expr: Variable: a3621
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Variable: a3500
                                                                      └──Type expr: Variable: a3621
                                                                └──Desc: Variable
                                                                   └──Variable: deval
                                                                   └──Type expr: Variable: a3621
                                                                   └──Type expr: Variable: a3500
                                                             └──Expression:
                                                                └──Type expr: Constructor: dterm
                                                                   └──Type expr: Variable: a3500
                                                                   └──Type expr: Variable: a3621
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: stack
                                                             └──Type expr: Variable: a3500
                                                          └──Desc: Variable
                                                             └──Variable: s
       └──Structure item: Type
          └──Type declaration:
             └──Type name: layout
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Empty_layout
                   └──Constructor alphas: env1 env2
                   └──Constructor type:
                      └──Type expr: Constructor: layout
                         └──Type expr: Variable: env1
                         └──Type expr: Variable: env2
                   └──Constraint:
                      └──Type expr: Variable: env2
                      └──Type expr: Constructor: unit
                └──Constructor declaration:
                   └──Constructor name: Push_layout
                   └──Constructor alphas: env1 env2
                   └──Constructor type:
                      └──Type expr: Constructor: layout
                         └──Type expr: Variable: env1
                         └──Type expr: Variable: env2
                   └──Constructor argument:
                      └──Constructor betas: t env21
                      └──Type expr: Tuple
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: t
                         └──Type expr: Constructor: layout
                            └──Type expr: Variable: env1
                            └──Type expr: Variable: env21
                         └──Type expr: Constructor: index
                            └──Type expr: Variable: env1
                            └──Type expr: Variable: t
                   └──Constraint:
                      └──Type expr: Variable: env2
                      └──Type expr: Tuple
                         └──Type expr: Variable: env21
                         └──Type expr: Variable: t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: size
                └──Abstraction:
                   └──Variables: a3675,a3674
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: layout
                            └──Type expr: Variable: a3696
                            └──Type expr: Variable: a3697
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: layout
                               └──Type expr: Variable: a3696
                               └──Type expr: Variable: a3697
                            └──Desc: Variable: l
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: layout
                                     └──Type expr: Variable: a3696
                                     └──Type expr: Variable: a3697
                                  └──Desc: Variable
                                     └──Variable: l
                               └──Type expr: Constructor: layout
                                  └──Type expr: Variable: a3696
                                  └──Type expr: Variable: a3697
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: a3696
                                           └──Type expr: Variable: a3697
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Empty_layout
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: a3696
                                                    └──Type expr: Variable: a3697
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 0
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: a3696
                                           └──Type expr: Variable: a3697
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Push_layout
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a3732
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: a3696
                                                       └──Type expr: Variable: a3730
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a3696
                                                       └──Type expr: Variable: a3732
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: a3696
                                                    └──Type expr: Variable: a3697
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a3732
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: a3696
                                                    └──Type expr: Variable: a3730
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: a3696
                                                    └──Type expr: Variable: a3732
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a3732
                                                    └──Desc: Any
                                                 └──Pattern:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: a3696
                                                       └──Type expr: Variable: a3730
                                                    └──Desc: Variable: l
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a3696
                                                       └──Type expr: Variable: a3732
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
                                                                └──Type expr: Variable: a3696
                                                                └──Type expr: Variable: a3730
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: size
                                                             └──Type expr: Variable: a3730
                                                             └──Type expr: Variable: a3696
                                                       └──Expression:
                                                          └──Type expr: Constructor: layout
                                                             └──Type expr: Variable: a3696
                                                             └──Type expr: Variable: a3730
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
                   └──Variables: a3781,a3784,a3783
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: layout
                            └──Type expr: Variable: a3811
                            └──Type expr: Variable: a3812
                         └──Type expr: Constructor: layout
                            └──Type expr: Tuple
                               └──Type expr: Variable: a3811
                               └──Type expr: Variable: a3843
                            └──Type expr: Variable: a3812
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: layout
                               └──Type expr: Variable: a3811
                               └──Type expr: Variable: a3812
                            └──Desc: Variable: l
                         └──Expression:
                            └──Type expr: Constructor: layout
                               └──Type expr: Tuple
                                  └──Type expr: Variable: a3811
                                  └──Type expr: Variable: a3843
                               └──Type expr: Variable: a3812
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: layout
                                     └──Type expr: Variable: a3811
                                     └──Type expr: Variable: a3812
                                  └──Desc: Variable
                                     └──Variable: l
                               └──Type expr: Constructor: layout
                                  └──Type expr: Variable: a3811
                                  └──Type expr: Variable: a3812
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: a3811
                                           └──Type expr: Variable: a3812
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Empty_layout
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: a3811
                                                    └──Type expr: Variable: a3812
                                     └──Expression:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a3811
                                              └──Type expr: Variable: a3843
                                           └──Type expr: Variable: a3812
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Empty_layout
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a3811
                                                       └──Type expr: Variable: a3843
                                                    └──Type expr: Variable: a3812
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: a3811
                                           └──Type expr: Variable: a3812
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Push_layout
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a3873
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: a3811
                                                       └──Type expr: Variable: a3871
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a3811
                                                       └──Type expr: Variable: a3873
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: a3811
                                                    └──Type expr: Variable: a3812
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a3873
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: a3811
                                                    └──Type expr: Variable: a3871
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: a3811
                                                    └──Type expr: Variable: a3873
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a3873
                                                    └──Desc: Variable: t
                                                 └──Pattern:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: a3811
                                                       └──Type expr: Variable: a3871
                                                    └──Desc: Variable: l
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a3811
                                                       └──Type expr: Variable: a3873
                                                    └──Desc: Variable: ix
                                     └──Expression:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a3811
                                              └──Type expr: Variable: a3843
                                           └──Type expr: Variable: a3812
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Push_layout
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a3873
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a3811
                                                          └──Type expr: Variable: a3843
                                                       └──Type expr: Variable: a3871
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a3811
                                                          └──Type expr: Variable: a3843
                                                       └──Type expr: Variable: a3873
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a3811
                                                       └──Type expr: Variable: a3843
                                                    └──Type expr: Variable: a3812
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a3873
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a3811
                                                       └──Type expr: Variable: a3843
                                                    └──Type expr: Variable: a3871
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a3811
                                                       └──Type expr: Variable: a3843
                                                    └──Type expr: Variable: a3873
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a3873
                                                    └──Desc: Variable
                                                       └──Variable: t
                                                 └──Expression:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a3811
                                                          └──Type expr: Variable: a3843
                                                       └──Type expr: Variable: a3871
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: a3811
                                                                └──Type expr: Variable: a3871
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a3811
                                                                   └──Type expr: Variable: a3843
                                                                └──Type expr: Variable: a3871
                                                          └──Desc: Variable
                                                             └──Variable: inc
                                                             └──Type expr: Variable: a3843
                                                             └──Type expr: Variable: a3871
                                                             └──Type expr: Variable: a3811
                                                       └──Expression:
                                                          └──Type expr: Constructor: layout
                                                             └──Type expr: Variable: a3811
                                                             └──Type expr: Variable: a3871
                                                          └──Desc: Variable
                                                             └──Variable: l
                                                 └──Expression:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a3811
                                                          └──Type expr: Variable: a3843
                                                       └──Type expr: Variable: a3873
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a3811
                                                                └──Type expr: Variable: a3873
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a3811
                                                                   └──Type expr: Variable: a3843
                                                                └──Type expr: Variable: a3873
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: a3811
                                                             └──Type expr: Variable: a3873
                                                          └──Desc: Variable
                                                             └──Variable: ix
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: prjl
                └──Abstraction:
                   └──Variables: a3962,a3961,a3965
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: a3997
                         └──Type expr: Arrow
                            └──Type expr: Constructor: int
                            └──Type expr: Arrow
                               └──Type expr: Constructor: layout
                                  └──Type expr: Variable: a4016
                                  └──Type expr: Variable: a4017
                               └──Type expr: Constructor: index
                                  └──Type expr: Variable: a4016
                                  └──Type expr: Variable: a3997
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: a3997
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: layout
                                     └──Type expr: Variable: a4016
                                     └──Type expr: Variable: a4017
                                  └──Type expr: Constructor: index
                                     └──Type expr: Variable: a4016
                                     └──Type expr: Variable: a3997
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable: n
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: layout
                                        └──Type expr: Variable: a4016
                                        └──Type expr: Variable: a4017
                                     └──Type expr: Constructor: index
                                        └──Type expr: Variable: a4016
                                        └──Type expr: Variable: a3997
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: a4016
                                           └──Type expr: Variable: a4017
                                        └──Desc: Variable: l
                                     └──Expression:
                                        └──Type expr: Constructor: index
                                           └──Type expr: Variable: a4016
                                           └──Type expr: Variable: a3997
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: layout
                                                 └──Type expr: Variable: a4016
                                                 └──Type expr: Variable: a4017
                                              └──Desc: Variable
                                                 └──Variable: l
                                           └──Type expr: Constructor: layout
                                              └──Type expr: Variable: a4016
                                              └──Type expr: Variable: a4017
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: a4016
                                                       └──Type expr: Variable: a4017
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Empty_layout
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: a4016
                                                                └──Type expr: Variable: a4017
                                                 └──Expression:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a4016
                                                       └──Type expr: Variable: a3997
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: string
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a4016
                                                                └──Type expr: Variable: a3997
                                                          └──Desc: Variable
                                                             └──Variable: fail_with
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a4016
                                                                └──Type expr: Variable: a3997
                                                       └──Expression:
                                                          └──Type expr: Constructor: string
                                                          └──Desc: Constant: convert prjl
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: a4016
                                                       └──Type expr: Variable: a4017
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Push_layout
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a4066
                                                                └──Type expr: Constructor: layout
                                                                   └──Type expr: Variable: a4016
                                                                   └──Type expr: Variable: a4064
                                                                └──Type expr: Constructor: index
                                                                   └──Type expr: Variable: a4016
                                                                   └──Type expr: Variable: a4066
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: a4016
                                                                └──Type expr: Variable: a4017
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a4066
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: a4016
                                                                └──Type expr: Variable: a4064
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a4016
                                                                └──Type expr: Variable: a4066
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a4066
                                                                └──Desc: Variable: t'
                                                             └──Pattern:
                                                                └──Type expr: Constructor: layout
                                                                   └──Type expr: Variable: a4016
                                                                   └──Type expr: Variable: a4064
                                                                └──Desc: Variable: l
                                                             └──Pattern:
                                                                └──Type expr: Constructor: index
                                                                   └──Type expr: Variable: a4016
                                                                   └──Type expr: Variable: a4066
                                                                └──Desc: Variable: ix
                                                 └──Expression:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a4016
                                                       └──Type expr: Variable: a3997
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
                                                             └──Type expr: Variable: a4016
                                                             └──Type expr: Variable: a3997
                                                          └──Desc: Match
                                                             └──Expression:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: a3997
                                                                   └──Type expr: Variable: a4066
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a4066
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: a3997
                                                                            └──Type expr: Variable: a4066
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: ty
                                                                                  └──Type expr: Variable: a3997
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: ty
                                                                                     └──Type expr: Variable: a4066
                                                                                  └──Type expr: Constructor: eq
                                                                                     └──Type expr: Variable: a3997
                                                                                     └──Type expr: Variable: a4066
                                                                            └──Desc: Variable
                                                                               └──Variable: check_eq
                                                                               └──Type expr: Variable: a4066
                                                                               └──Type expr: Variable: a3997
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: a3997
                                                                            └──Desc: Variable
                                                                               └──Variable: t
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a4066
                                                                      └──Desc: Variable
                                                                         └──Variable: t'
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a3997
                                                                └──Type expr: Variable: a4066
                                                             └──Cases:
                                                                └──Case:
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: eq
                                                                         └──Type expr: Variable: a3997
                                                                         └──Type expr: Variable: a4066
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Refl
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: eq
                                                                                  └──Type expr: Variable: a3997
                                                                                  └──Type expr: Variable: a4066
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: index
                                                                         └──Type expr: Variable: a4016
                                                                         └──Type expr: Variable: a3997
                                                                      └──Desc: Variable
                                                                         └──Variable: ix
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: a4016
                                                             └──Type expr: Variable: a3997
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: layout
                                                                      └──Type expr: Variable: a4016
                                                                      └──Type expr: Variable: a4064
                                                                   └──Type expr: Constructor: index
                                                                      └──Type expr: Variable: a4016
                                                                      └──Type expr: Variable: a3997
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: int
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: layout
                                                                               └──Type expr: Variable: a4016
                                                                               └──Type expr: Variable: a4064
                                                                            └──Type expr: Constructor: index
                                                                               └──Type expr: Variable: a4016
                                                                               └──Type expr: Variable: a3997
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: ty
                                                                                  └──Type expr: Variable: a3997
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: int
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: layout
                                                                                        └──Type expr: Variable: a4016
                                                                                        └──Type expr: Variable: a4064
                                                                                     └──Type expr: Constructor: index
                                                                                        └──Type expr: Variable: a4016
                                                                                        └──Type expr: Variable: a3997
                                                                            └──Desc: Variable
                                                                               └──Variable: prjl
                                                                               └──Type expr: Variable: a4064
                                                                               └──Type expr: Variable: a4016
                                                                               └──Type expr: Variable: a3997
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: a3997
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
                                                                   └──Type expr: Variable: a4016
                                                                   └──Type expr: Variable: a4064
                                                                └──Desc: Variable
                                                                   └──Variable: l
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: convert
                └──Abstraction:
                   └──Variables: a4191,a4194
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: layout
                            └──Type expr: Variable: a4223
                            └──Type expr: Variable: a4223
                         └──Type expr: Arrow
                            └──Type expr: Constructor: hterm
                               └──Type expr: Variable: a4233
                            └──Type expr: Constructor: dterm
                               └──Type expr: Variable: a4223
                               └──Type expr: Variable: a4233
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: layout
                               └──Type expr: Variable: a4223
                               └──Type expr: Variable: a4223
                            └──Desc: Variable: l
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: hterm
                                  └──Type expr: Variable: a4233
                               └──Type expr: Constructor: dterm
                                  └──Type expr: Variable: a4223
                                  └──Type expr: Variable: a4233
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: hterm
                                     └──Type expr: Variable: a4233
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Constructor: dterm
                                     └──Type expr: Variable: a4223
                                     └──Type expr: Variable: a4233
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: a4233
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Constructor: hterm
                                        └──Type expr: Variable: a4233
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: hterm
                                                 └──Type expr: Variable: a4233
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Tag
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a4233
                                                          └──Type expr: Constructor: int
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a4233
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: a4233
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a4233
                                                          └──Desc: Variable: t
                                                       └──Pattern:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable: sz
                                           └──Expression:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a4223
                                                 └──Type expr: Variable: a4233
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: index
                                                          └──Type expr: Variable: a4223
                                                          └──Type expr: Variable: a4233
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a4223
                                                          └──Type expr: Variable: a4233
                                                 └──Expression:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a4223
                                                       └──Type expr: Variable: a4233
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: a4223
                                                                └──Type expr: Variable: a4223
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a4223
                                                                └──Type expr: Variable: a4233
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: int
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Variable: a4223
                                                                         └──Type expr: Variable: a4223
                                                                      └──Type expr: Constructor: index
                                                                         └──Type expr: Variable: a4223
                                                                         └──Type expr: Variable: a4233
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a4233
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: int
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: layout
                                                                                  └──Type expr: Variable: a4223
                                                                                  └──Type expr: Variable: a4223
                                                                               └──Type expr: Constructor: index
                                                                                  └──Type expr: Variable: a4223
                                                                                  └──Type expr: Variable: a4233
                                                                      └──Desc: Variable
                                                                         └──Variable: prjl
                                                                         └──Type expr: Variable: a4223
                                                                         └──Type expr: Variable: a4223
                                                                         └──Type expr: Variable: a4233
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a4233
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
                                                                                                    └──Type expr: Variable: a4223
                                                                                                    └──Type expr: Variable: a4223
                                                                                                 └──Type expr: Constructor: int
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: size
                                                                                                 └──Type expr: Variable: a4223
                                                                                                 └──Type expr: Variable: a4223
                                                                                           └──Expression:
                                                                                              └──Type expr: Constructor: layout
                                                                                                 └──Type expr: Variable: a4223
                                                                                                 └──Type expr: Variable: a4223
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
                                                             └──Type expr: Variable: a4223
                                                             └──Type expr: Variable: a4223
                                                          └──Desc: Variable
                                                             └──Variable: l
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: hterm
                                                 └──Type expr: Variable: a4233
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Con
                                                    └──Constructor argument type:
                                                       └──Type expr: Variable: a4233
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a4233
                                                 └──Pattern:
                                                    └──Type expr: Variable: a4233
                                                    └──Desc: Variable: v
                                           └──Expression:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a4223
                                                 └──Type expr: Variable: a4233
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_con
                                                    └──Constructor argument type:
                                                       └──Type expr: Variable: a4233
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a4223
                                                          └──Type expr: Variable: a4233
                                                 └──Expression:
                                                    └──Type expr: Variable: a4233
                                                    └──Desc: Variable
                                                       └──Variable: v
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: hterm
                                                 └──Type expr: Variable: a4233
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Lam
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a4372
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: a4372
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: a4368
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a4233
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: a4372
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: a4372
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: a4368
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a4372
                                                          └──Desc: Variable: t
                                                       └──Pattern:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: a4372
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: a4368
                                                          └──Desc: Variable: f
                                           └──Expression:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a4223
                                                 └──Type expr: Variable: a4233
                                              └──Desc: Let
                                                 └──Value bindings:
                                                    └──Value binding:
                                                       └──Pattern:
                                                          └──Type expr: Constructor: layout
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a4223
                                                                └──Type expr: Variable: a4372
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a4223
                                                                └──Type expr: Variable: a4372
                                                          └──Desc: Variable: l'
                                                       └──Abstraction:
                                                          └──Variables:
                                                          └──Expression:
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a4223
                                                                   └──Type expr: Variable: a4372
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a4223
                                                                   └──Type expr: Variable: a4372
                                                             └──Desc: Construct
                                                                └──Constructor description:
                                                                   └──Name: Push_layout
                                                                   └──Constructor argument type:
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a4372
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a4223
                                                                               └──Type expr: Variable: a4372
                                                                            └──Type expr: Variable: a4223
                                                                         └──Type expr: Constructor: index
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a4223
                                                                               └──Type expr: Variable: a4372
                                                                            └──Type expr: Variable: a4372
                                                                   └──Constructor type:
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a4223
                                                                            └──Type expr: Variable: a4372
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a4223
                                                                            └──Type expr: Variable: a4372
                                                                └──Expression:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a4372
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a4223
                                                                            └──Type expr: Variable: a4372
                                                                         └──Type expr: Variable: a4223
                                                                      └──Type expr: Constructor: index
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a4223
                                                                            └──Type expr: Variable: a4372
                                                                         └──Type expr: Variable: a4372
                                                                   └──Desc: Tuple
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a4372
                                                                         └──Desc: Variable
                                                                            └──Variable: t
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a4223
                                                                               └──Type expr: Variable: a4372
                                                                            └──Type expr: Variable: a4223
                                                                         └──Desc: Application
                                                                            └──Expression:
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: layout
                                                                                     └──Type expr: Variable: a4223
                                                                                     └──Type expr: Variable: a4223
                                                                                  └──Type expr: Constructor: layout
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Variable: a4223
                                                                                        └──Type expr: Variable: a4372
                                                                                     └──Type expr: Variable: a4223
                                                                               └──Desc: Variable
                                                                                  └──Variable: inc
                                                                                  └──Type expr: Variable: a4372
                                                                                  └──Type expr: Variable: a4223
                                                                                  └──Type expr: Variable: a4223
                                                                            └──Expression:
                                                                               └──Type expr: Constructor: layout
                                                                                  └──Type expr: Variable: a4223
                                                                                  └──Type expr: Variable: a4223
                                                                               └──Desc: Variable
                                                                                  └──Variable: l
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: index
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a4223
                                                                               └──Type expr: Variable: a4372
                                                                            └──Type expr: Variable: a4372
                                                                         └──Desc: Construct
                                                                            └──Constructor description:
                                                                               └──Name: Zero
                                                                               └──Constructor argument type:
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Constructor type:
                                                                                  └──Type expr: Constructor: index
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Variable: a4223
                                                                                        └──Type expr: Variable: a4372
                                                                                     └──Type expr: Variable: a4372
                                                                            └──Expression:
                                                                               └──Type expr: Constructor: unit
                                                                               └──Desc: Constant: ()
                                                 └──Expression:
                                                    └──Type expr: Constructor: dterm
                                                       └──Type expr: Variable: a4223
                                                       └──Type expr: Variable: a4233
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: D_lam
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: dterm
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a4223
                                                                   └──Type expr: Variable: a4372
                                                                └──Type expr: Variable: a4368
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: dterm
                                                                └──Type expr: Variable: a4223
                                                                └──Type expr: Variable: a4233
                                                       └──Expression:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a4223
                                                                └──Type expr: Variable: a4372
                                                             └──Type expr: Variable: a4368
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: hterm
                                                                      └──Type expr: Variable: a4368
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a4223
                                                                         └──Type expr: Variable: a4372
                                                                      └──Type expr: Variable: a4368
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a4223
                                                                               └──Type expr: Variable: a4372
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a4223
                                                                               └──Type expr: Variable: a4372
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: hterm
                                                                               └──Type expr: Variable: a4368
                                                                            └──Type expr: Constructor: dterm
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: a4223
                                                                                  └──Type expr: Variable: a4372
                                                                               └──Type expr: Variable: a4368
                                                                      └──Desc: Variable
                                                                         └──Variable: convert
                                                                         └──Type expr: Variable: a4368
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a4223
                                                                            └──Type expr: Variable: a4372
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a4223
                                                                            └──Type expr: Variable: a4372
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a4223
                                                                            └──Type expr: Variable: a4372
                                                                      └──Desc: Variable
                                                                         └──Variable: l'
                                                             └──Expression:
                                                                └──Type expr: Constructor: hterm
                                                                   └──Type expr: Variable: a4368
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: hterm
                                                                            └──Type expr: Variable: a4372
                                                                         └──Type expr: Constructor: hterm
                                                                            └──Type expr: Variable: a4368
                                                                      └──Desc: Variable
                                                                         └──Variable: f
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: hterm
                                                                         └──Type expr: Variable: a4372
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Tag
                                                                            └──Constructor argument type:
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Constructor: ty
                                                                                     └──Type expr: Variable: a4372
                                                                                  └──Type expr: Constructor: int
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: hterm
                                                                                  └──Type expr: Variable: a4372
                                                                         └──Expression:
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Constructor: ty
                                                                                  └──Type expr: Variable: a4372
                                                                               └──Type expr: Constructor: int
                                                                            └──Desc: Tuple
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: ty
                                                                                     └──Type expr: Variable: a4372
                                                                                  └──Desc: Variable
                                                                                     └──Variable: t
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: int
                                                                                  └──Desc: Application
                                                                                     └──Expression:
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Constructor: layout
                                                                                              └──Type expr: Variable: a4223
                                                                                              └──Type expr: Variable: a4223
                                                                                           └──Type expr: Constructor: int
                                                                                        └──Desc: Variable
                                                                                           └──Variable: size
                                                                                           └──Type expr: Variable: a4223
                                                                                           └──Type expr: Variable: a4223
                                                                                     └──Expression:
                                                                                        └──Type expr: Constructor: layout
                                                                                           └──Type expr: Variable: a4223
                                                                                           └──Type expr: Variable: a4223
                                                                                        └──Desc: Variable
                                                                                           └──Variable: l
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: hterm
                                                 └──Type expr: Variable: a4233
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: App
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a4510
                                                                └──Type expr: Variable: a4233
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: a4510
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a4233
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a4510
                                                             └──Type expr: Variable: a4233
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a4510
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a4510
                                                                └──Type expr: Variable: a4233
                                                          └──Desc: Variable: f
                                                       └──Pattern:
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: a4510
                                                          └──Desc: Variable: a
                                           └──Expression:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a4223
                                                 └──Type expr: Variable: a4233
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_app
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a4223
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a4510
                                                                └──Type expr: Variable: a4233
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a4223
                                                             └──Type expr: Variable: a4510
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a4223
                                                          └──Type expr: Variable: a4233
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a4223
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a4510
                                                             └──Type expr: Variable: a4233
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a4223
                                                          └──Type expr: Variable: a4510
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a4223
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a4510
                                                                └──Type expr: Variable: a4233
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: hterm
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: a4510
                                                                         └──Type expr: Variable: a4233
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Variable: a4223
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: a4510
                                                                         └──Type expr: Variable: a4233
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Variable: a4223
                                                                            └──Type expr: Variable: a4223
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: hterm
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: a4510
                                                                                  └──Type expr: Variable: a4233
                                                                            └──Type expr: Constructor: dterm
                                                                               └──Type expr: Variable: a4223
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: a4510
                                                                                  └──Type expr: Variable: a4233
                                                                      └──Desc: Variable
                                                                         └──Variable: convert
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Variable: a4510
                                                                            └──Type expr: Variable: a4233
                                                                         └──Type expr: Variable: a4223
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Variable: a4223
                                                                         └──Type expr: Variable: a4223
                                                                      └──Desc: Variable
                                                                         └──Variable: l
                                                             └──Expression:
                                                                └──Type expr: Constructor: hterm
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a4510
                                                                      └──Type expr: Variable: a4233
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a4223
                                                             └──Type expr: Variable: a4510
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: hterm
                                                                      └──Type expr: Variable: a4510
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Variable: a4223
                                                                      └──Type expr: Variable: a4510
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Variable: a4223
                                                                            └──Type expr: Variable: a4223
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: hterm
                                                                               └──Type expr: Variable: a4510
                                                                            └──Type expr: Constructor: dterm
                                                                               └──Type expr: Variable: a4223
                                                                               └──Type expr: Variable: a4510
                                                                      └──Desc: Variable
                                                                         └──Variable: convert
                                                                         └──Type expr: Variable: a4510
                                                                         └──Type expr: Variable: a4223
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Variable: a4223
                                                                         └──Type expr: Variable: a4223
                                                                      └──Desc: Variable
                                                                         └──Variable: l
                                                             └──Expression:
                                                                └──Type expr: Constructor: hterm
                                                                   └──Type expr: Variable: a4510
                                                                └──Desc: Variable
                                                                   └──Variable: a |}]