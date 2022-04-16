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
                   └──Constructor alphas: 10034
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 10034
                   └──Constraint:
                      └──Type expr: Variable: 10034
                      └──Type expr: Constructor: int
                └──Constructor declaration:
                   └──Constructor name: String
                   └──Constructor alphas: 10034
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 10034
                   └──Constraint:
                      └──Type expr: Variable: 10034
                      └──Type expr: Constructor: string
                └──Constructor declaration:
                   └──Constructor name: List
                   └──Constructor alphas: 10034
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 10034
                   └──Constructor argument:
                      └──Constructor betas: 10039
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 10039
                   └──Constraint:
                      └──Type expr: Variable: 10034
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 10039
                └──Constructor declaration:
                   └──Constructor name: Pair
                   └──Constructor alphas: 10034
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 10034
                   └──Constructor argument:
                      └──Constructor betas: 10044 10043
                      └──Type expr: Tuple
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 10043
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 10044
                   └──Constraint:
                      └──Type expr: Variable: 10034
                      └──Type expr: Tuple
                         └──Type expr: Variable: 10043
                         └──Type expr: Variable: 10044
                └──Constructor declaration:
                   └──Constructor name: Fun
                   └──Constructor alphas: 10034
                   └──Constructor type:
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 10034
                   └──Constructor argument:
                      └──Constructor betas: 10051 10050
                      └──Type expr: Tuple
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 10050
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 10051
                   └──Constraint:
                      └──Type expr: Variable: 10034
                      └──Type expr: Arrow
                         └──Type expr: Variable: 10050
                         └──Type expr: Variable: 10051
       └──Structure item: Type
          └──Type declaration:
             └──Type name: eq
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Refl
                   └──Constructor alphas: 10057 10058
                   └──Constructor type:
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: 10057
                         └──Type expr: Variable: 10058
                   └──Constraint:
                      └──Type expr: Variable: 10057
                      └──Type expr: Variable: 10058
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
                   └──Variables: 10141,10143
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 10169
                         └──Type expr: Arrow
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: 10179
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: 10169
                               └──Type expr: Variable: 10179
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: 10169
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: ty
                                  └──Type expr: Variable: 10179
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: 10169
                                  └──Type expr: Variable: 10179
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: ty
                                     └──Type expr: Variable: 10179
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: 10169
                                     └──Type expr: Variable: 10179
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: ty
                                              └──Type expr: Variable: 10169
                                           └──Type expr: Constructor: ty
                                              └──Type expr: Variable: 10179
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: 10169
                                              └──Desc: Variable
                                                 └──Variable: t1
                                           └──Expression:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: 10179
                                              └──Desc: Variable
                                                 └──Variable: t2
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: ty
                                           └──Type expr: Variable: 10169
                                        └──Type expr: Constructor: ty
                                           └──Type expr: Variable: 10179
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 10169
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 10179
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 10169
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 10169
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 10179
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 10179
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: 10169
                                                 └──Type expr: Variable: 10179
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Refl
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: 10169
                                                          └──Type expr: Variable: 10169
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 10169
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 10179
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 10169
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: String
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 10169
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 10179
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: String
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 10179
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: 10169
                                                 └──Type expr: Variable: 10179
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Refl
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: 10169
                                                          └──Type expr: Variable: 10169
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 10169
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 10179
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 10169
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: List
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 10261
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 10169
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: 10261
                                                          └──Desc: Variable: t1
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 10179
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: List
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 10258
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 10179
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: 10258
                                                          └──Desc: Variable: t2
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: 10169
                                                 └──Type expr: Variable: 10179
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: 10261
                                                       └──Type expr: Variable: 10258
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 10258
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: 10261
                                                                └──Type expr: Variable: 10258
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: 10261
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: 10258
                                                                      └──Type expr: Constructor: eq
                                                                         └──Type expr: Variable: 10261
                                                                         └──Type expr: Variable: 10258
                                                                └──Desc: Variable
                                                                   └──Variable: check_eq
                                                                   └──Type expr: Variable: 10258
                                                                   └──Type expr: Variable: 10261
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 10261
                                                                └──Desc: Variable
                                                                   └──Variable: t1
                                                       └──Expression:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: 10258
                                                          └──Desc: Variable
                                                             └──Variable: t2
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: 10261
                                                    └──Type expr: Variable: 10258
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: 10261
                                                             └──Type expr: Variable: 10258
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Refl
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: 10261
                                                                      └──Type expr: Variable: 10258
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: 10169
                                                             └──Type expr: Variable: 10179
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Refl
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: 10169
                                                                      └──Type expr: Variable: 10169
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 10169
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 10179
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 10169
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Pair
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 10343
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 10341
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 10169
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 10343
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 10341
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 10343
                                                                └──Desc: Variable: t11
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 10341
                                                                └──Desc: Variable: t12
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 10179
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Pair
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 10337
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 10335
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 10179
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 10337
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 10335
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 10337
                                                                └──Desc: Variable: t21
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 10335
                                                                └──Desc: Variable: t22
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: 10169
                                                 └──Type expr: Variable: 10179
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: 10343
                                                          └──Type expr: Variable: 10337
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: 10341
                                                          └──Type expr: Variable: 10335
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: 10343
                                                             └──Type expr: Variable: 10337
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: 10337
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: 10343
                                                                      └──Type expr: Variable: 10337
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: 10343
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: 10337
                                                                            └──Type expr: Constructor: eq
                                                                               └──Type expr: Variable: 10343
                                                                               └──Type expr: Variable: 10337
                                                                      └──Desc: Variable
                                                                         └──Variable: check_eq
                                                                         └──Type expr: Variable: 10337
                                                                         └──Type expr: Variable: 10343
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: 10343
                                                                      └──Desc: Variable
                                                                         └──Variable: t11
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 10337
                                                                └──Desc: Variable
                                                                   └──Variable: t21
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: 10341
                                                             └──Type expr: Variable: 10335
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: 10335
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: 10341
                                                                      └──Type expr: Variable: 10335
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: 10341
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: 10335
                                                                            └──Type expr: Constructor: eq
                                                                               └──Type expr: Variable: 10341
                                                                               └──Type expr: Variable: 10335
                                                                      └──Desc: Variable
                                                                         └──Variable: check_eq
                                                                         └──Type expr: Variable: 10335
                                                                         └──Type expr: Variable: 10341
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: 10341
                                                                      └──Desc: Variable
                                                                         └──Variable: t12
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 10335
                                                                └──Desc: Variable
                                                                   └──Variable: t22
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: 10343
                                                       └──Type expr: Variable: 10337
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: 10341
                                                       └──Type expr: Variable: 10335
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: 10343
                                                                └──Type expr: Variable: 10337
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: 10341
                                                                └──Type expr: Variable: 10335
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: 10343
                                                                   └──Type expr: Variable: 10337
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: 10343
                                                                            └──Type expr: Variable: 10337
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: 10341
                                                                   └──Type expr: Variable: 10335
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: 10341
                                                                            └──Type expr: Variable: 10335
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: 10169
                                                             └──Type expr: Variable: 10179
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Refl
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: 10169
                                                                      └──Type expr: Variable: 10169
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 10169
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 10179
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 10169
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fun
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 10464
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 10462
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 10169
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 10464
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 10462
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 10464
                                                                └──Desc: Variable: t11
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 10462
                                                                └──Desc: Variable: t12
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 10179
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fun
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 10458
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 10456
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 10179
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 10458
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 10456
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 10458
                                                                └──Desc: Variable: t21
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 10456
                                                                └──Desc: Variable: t22
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: 10169
                                                 └──Type expr: Variable: 10179
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: 10464
                                                          └──Type expr: Variable: 10458
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: 10462
                                                          └──Type expr: Variable: 10456
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: 10464
                                                             └──Type expr: Variable: 10458
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: 10458
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: 10464
                                                                      └──Type expr: Variable: 10458
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: 10464
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: 10458
                                                                            └──Type expr: Constructor: eq
                                                                               └──Type expr: Variable: 10464
                                                                               └──Type expr: Variable: 10458
                                                                      └──Desc: Variable
                                                                         └──Variable: check_eq
                                                                         └──Type expr: Variable: 10458
                                                                         └──Type expr: Variable: 10464
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: 10464
                                                                      └──Desc: Variable
                                                                         └──Variable: t11
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 10458
                                                                └──Desc: Variable
                                                                   └──Variable: t21
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: 10462
                                                             └──Type expr: Variable: 10456
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: 10456
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: 10462
                                                                      └──Type expr: Variable: 10456
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: 10462
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: 10456
                                                                            └──Type expr: Constructor: eq
                                                                               └──Type expr: Variable: 10462
                                                                               └──Type expr: Variable: 10456
                                                                      └──Desc: Variable
                                                                         └──Variable: check_eq
                                                                         └──Type expr: Variable: 10456
                                                                         └──Type expr: Variable: 10462
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: 10462
                                                                      └──Desc: Variable
                                                                         └──Variable: t12
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 10456
                                                                └──Desc: Variable
                                                                   └──Variable: t22
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: 10464
                                                       └──Type expr: Variable: 10458
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: 10462
                                                       └──Type expr: Variable: 10456
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: 10464
                                                                └──Type expr: Variable: 10458
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: 10462
                                                                └──Type expr: Variable: 10456
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: 10464
                                                                   └──Type expr: Variable: 10458
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: 10464
                                                                            └──Type expr: Variable: 10458
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: 10462
                                                                   └──Type expr: Variable: 10456
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: 10462
                                                                            └──Type expr: Variable: 10456
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: 10169
                                                             └──Type expr: Variable: 10179
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Refl
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: 10169
                                                                      └──Type expr: Variable: 10169
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: 10571
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 10581
                         └──Type expr: Arrow
                            └──Type expr: Variable: 10571
                            └──Type expr: Variable: 10581
                   └──Desc: Variable: cast
                └──Abstraction:
                   └──Variables: 10571,10581
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 10571
                         └──Type expr: Arrow
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: 10581
                            └──Type expr: Arrow
                               └──Type expr: Variable: 10571
                               └──Type expr: Variable: 10581
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: 10571
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: ty
                                  └──Type expr: Variable: 10581
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 10571
                                  └──Type expr: Variable: 10581
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: ty
                                     └──Type expr: Variable: 10581
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 10571
                                     └──Type expr: Variable: 10581
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: 10571
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: 10581
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: 10571
                                                 └──Type expr: Variable: 10581
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: 10581
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: 10571
                                                          └──Type expr: Variable: 10581
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 10571
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 10581
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: 10571
                                                                   └──Type expr: Variable: 10581
                                                          └──Desc: Variable
                                                             └──Variable: check_eq
                                                             └──Type expr: Variable: 10581
                                                             └──Type expr: Variable: 10571
                                                       └──Expression:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: 10571
                                                          └──Desc: Variable
                                                             └──Variable: t1
                                                 └──Expression:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 10581
                                                    └──Desc: Variable
                                                       └──Variable: t2
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: 10571
                                              └──Type expr: Variable: 10581
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: 10571
                                                       └──Type expr: Variable: 10581
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Refl
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: 10571
                                                                └──Type expr: Variable: 10581
                                                 └──Expression:
                                                    └──Type expr: Variable: 10581
                                                    └──Desc: Variable
                                                       └──Variable: x
       └──Structure item: Type
          └──Type declaration:
             └──Type name: hterm
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Tag
                   └──Constructor alphas: 10061
                   └──Constructor type:
                      └──Type expr: Constructor: hterm
                         └──Type expr: Variable: 10061
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 10061
                         └──Type expr: Constructor: int
                └──Constructor declaration:
                   └──Constructor name: Con
                   └──Constructor alphas: 10061
                   └──Constructor type:
                      └──Type expr: Constructor: hterm
                         └──Type expr: Variable: 10061
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: 10061
                └──Constructor declaration:
                   └──Constructor name: Lam
                   └──Constructor alphas: 10061
                   └──Constructor type:
                      └──Type expr: Constructor: hterm
                         └──Type expr: Variable: 10061
                   └──Constructor argument:
                      └──Constructor betas: 10068 10067
                      └──Type expr: Tuple
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 10067
                         └──Type expr: Arrow
                            └──Type expr: Constructor: hterm
                               └──Type expr: Variable: 10067
                            └──Type expr: Constructor: hterm
                               └──Type expr: Variable: 10068
                   └──Constraint:
                      └──Type expr: Variable: 10061
                      └──Type expr: Arrow
                         └──Type expr: Variable: 10067
                         └──Type expr: Variable: 10068
                └──Constructor declaration:
                   └──Constructor name: App
                   └──Constructor alphas: 10061
                   └──Constructor type:
                      └──Type expr: Constructor: hterm
                         └──Type expr: Variable: 10061
                   └──Constructor argument:
                      └──Constructor betas: 10076
                      └──Type expr: Tuple
                         └──Type expr: Constructor: hterm
                            └──Type expr: Arrow
                               └──Type expr: Variable: 10076
                               └──Type expr: Variable: 10061
                         └──Type expr: Constructor: hterm
                            └──Type expr: Variable: 10076
       └──Structure item: Primitive
          └──Value description:
             └──Name: fail_with
             └──Scheme:
                └──Variables: 10621
                └──Type expr: Arrow
                   └──Type expr: Constructor: string
                   └──Type expr: Variable: 10621
             └──Primitive name: %fail_with
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: heval
                └──Abstraction:
                   └──Variables: 10630
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: hterm
                            └──Type expr: Variable: 10647
                         └──Type expr: Variable: 10647
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: hterm
                               └──Type expr: Variable: 10647
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Variable: 10647
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: hterm
                                     └──Type expr: Variable: 10647
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: hterm
                                  └──Type expr: Variable: 10647
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: 10647
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Tag
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 10647
                                                    └──Type expr: Constructor: int
                                              └──Constructor type:
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: 10647
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 10647
                                                 └──Type expr: Constructor: int
                                              └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Variable: 10647
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: string
                                                 └──Type expr: Variable: 10647
                                              └──Desc: Variable
                                                 └──Variable: fail_with
                                                 └──Type expr: Variable: 10647
                                           └──Expression:
                                              └──Type expr: Constructor: string
                                              └──Desc: Constant: HOAS eval
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: 10647
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Con
                                              └──Constructor argument type:
                                                 └──Type expr: Variable: 10647
                                              └──Constructor type:
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: 10647
                                           └──Pattern:
                                              └──Type expr: Variable: 10647
                                              └──Desc: Variable: v
                                     └──Expression:
                                        └──Type expr: Variable: 10647
                                        └──Desc: Variable
                                           └──Variable: v
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: 10647
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Lam
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 10696
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: 10696
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: 10692
                                              └──Constructor type:
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: 10647
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 10696
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: 10696
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: 10692
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 10696
                                                    └──Desc: Any
                                                 └──Pattern:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: 10696
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: 10692
                                                    └──Desc: Variable: f
                                     └──Expression:
                                        └──Type expr: Variable: 10647
                                        └──Desc: Function
                                           └──Pattern:
                                              └──Type expr: Variable: 10696
                                              └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Variable: 10692
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: 10692
                                                       └──Type expr: Variable: 10692
                                                    └──Desc: Variable
                                                       └──Variable: heval
                                                       └──Type expr: Variable: 10692
                                                 └──Expression:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: 10692
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: 10696
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: 10692
                                                          └──Desc: Variable
                                                             └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: 10696
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Con
                                                                └──Constructor argument type:
                                                                   └──Type expr: Variable: 10696
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: hterm
                                                                      └──Type expr: Variable: 10696
                                                             └──Expression:
                                                                └──Type expr: Variable: 10696
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: 10647
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: App
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: 10744
                                                          └──Type expr: Variable: 10647
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: 10744
                                              └──Constructor type:
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: 10647
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 10744
                                                       └──Type expr: Variable: 10647
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: 10744
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: 10744
                                                          └──Type expr: Variable: 10647
                                                    └──Desc: Variable: f
                                                 └──Pattern:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: 10744
                                                    └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: 10647
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: 10744
                                                 └──Type expr: Variable: 10647
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 10744
                                                             └──Type expr: Variable: 10647
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: 10744
                                                          └──Type expr: Variable: 10647
                                                    └──Desc: Variable
                                                       └──Variable: heval
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: 10744
                                                          └──Type expr: Variable: 10647
                                                 └──Expression:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: 10744
                                                          └──Type expr: Variable: 10647
                                                    └──Desc: Variable
                                                       └──Variable: f
                                           └──Expression:
                                              └──Type expr: Variable: 10744
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: 10744
                                                       └──Type expr: Variable: 10744
                                                    └──Desc: Variable
                                                       └──Variable: heval
                                                       └──Type expr: Variable: 10744
                                                 └──Expression:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: 10744
                                                    └──Desc: Variable
                                                       └──Variable: x
       └──Structure item: Type
          └──Type declaration:
             └──Type name: index
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Zero
                   └──Constructor alphas: 10082 10083
                   └──Constructor type:
                      └──Type expr: Constructor: index
                         └──Type expr: Variable: 10082
                         └──Type expr: Variable: 10083
                   └──Constructor argument:
                      └──Constructor betas: 10084
                      └──Type expr: Constructor: unit
                   └──Constraint:
                      └──Type expr: Variable: 10082
                      └──Type expr: Tuple
                         └──Type expr: Variable: 10084
                         └──Type expr: Variable: 10083
                └──Constructor declaration:
                   └──Constructor name: Succ
                   └──Constructor alphas: 10082 10083
                   └──Constructor type:
                      └──Type expr: Constructor: index
                         └──Type expr: Variable: 10082
                         └──Type expr: Variable: 10083
                   └──Constructor argument:
                      └──Constructor betas: 10089 10088
                      └──Type expr: Constructor: index
                         └──Type expr: Variable: 10088
                         └──Type expr: Variable: 10083
                   └──Constraint:
                      └──Type expr: Variable: 10082
                      └──Type expr: Tuple
                         └──Type expr: Variable: 10088
                         └──Type expr: Variable: 10089
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: index_to_int
                └──Abstraction:
                   └──Variables: 10781,10780
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: index
                            └──Type expr: Variable: 10802
                            └──Type expr: Variable: 10803
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: index
                               └──Type expr: Variable: 10802
                               └──Type expr: Variable: 10803
                            └──Desc: Variable: ix
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: index
                                     └──Type expr: Variable: 10802
                                     └──Type expr: Variable: 10803
                                  └──Desc: Variable
                                     └──Variable: ix
                               └──Type expr: Constructor: index
                                  └──Type expr: Variable: 10802
                                  └──Type expr: Variable: 10803
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: index
                                           └──Type expr: Variable: 10802
                                           └──Type expr: Variable: 10803
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Zero
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: 10802
                                                    └──Type expr: Variable: 10803
                                           └──Pattern:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 0
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: index
                                           └──Type expr: Variable: 10802
                                           └──Type expr: Variable: 10803
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: 10832
                                                    └──Type expr: Variable: 10803
                                              └──Constructor type:
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: 10802
                                                    └──Type expr: Variable: 10803
                                           └──Pattern:
                                              └──Type expr: Constructor: index
                                                 └──Type expr: Variable: 10832
                                                 └──Type expr: Variable: 10803
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
                                                                └──Type expr: Variable: 10832
                                                                └──Type expr: Variable: 10803
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: index_to_int
                                                             └──Type expr: Variable: 10803
                                                             └──Type expr: Variable: 10832
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: 10832
                                                             └──Type expr: Variable: 10803
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
                   └──Constructor alphas: 10093
                   └──Constructor type:
                      └──Type expr: Constructor: stack
                         └──Type expr: Variable: 10093
                   └──Constraint:
                      └──Type expr: Variable: 10093
                      └──Type expr: Constructor: unit
                └──Constructor declaration:
                   └──Constructor name: Push
                   └──Constructor alphas: 10093
                   └──Constructor type:
                      └──Type expr: Constructor: stack
                         └──Type expr: Variable: 10093
                   └──Constructor argument:
                      └──Constructor betas: 10097 10096
                      └──Type expr: Tuple
                         └──Type expr: Constructor: stack
                            └──Type expr: Variable: 10096
                         └──Type expr: Variable: 10097
                   └──Constraint:
                      └──Type expr: Variable: 10093
                      └──Type expr: Tuple
                         └──Type expr: Variable: 10096
                         └──Type expr: Variable: 10097
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: prj
                └──Abstraction:
                   └──Variables: 10881,10880
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: index
                            └──Type expr: Variable: 10906
                            └──Type expr: Variable: 10907
                         └──Type expr: Arrow
                            └──Type expr: Constructor: stack
                               └──Type expr: Variable: 10906
                            └──Type expr: Variable: 10907
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: index
                               └──Type expr: Variable: 10906
                               └──Type expr: Variable: 10907
                            └──Desc: Variable: ix
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: stack
                                  └──Type expr: Variable: 10906
                               └──Type expr: Variable: 10907
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: stack
                                     └──Type expr: Variable: 10906
                                  └──Desc: Variable: s
                               └──Expression:
                                  └──Type expr: Variable: 10907
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: index
                                              └──Type expr: Variable: 10906
                                              └──Type expr: Variable: 10907
                                           └──Type expr: Constructor: stack
                                              └──Type expr: Variable: 10906
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: index
                                                 └──Type expr: Variable: 10906
                                                 └──Type expr: Variable: 10907
                                              └──Desc: Variable
                                                 └──Variable: ix
                                           └──Expression:
                                              └──Type expr: Constructor: stack
                                                 └──Type expr: Variable: 10906
                                              └──Desc: Variable
                                                 └──Variable: s
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: index
                                           └──Type expr: Variable: 10906
                                           └──Type expr: Variable: 10907
                                        └──Type expr: Constructor: stack
                                           └──Type expr: Variable: 10906
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: 10906
                                                    └──Type expr: Variable: 10907
                                                 └──Type expr: Constructor: stack
                                                    └──Type expr: Variable: 10906
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: 10906
                                                       └──Type expr: Variable: 10907
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: 10906
                                                                └──Type expr: Variable: 10907
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                                 └──Pattern:
                                                    └──Type expr: Constructor: stack
                                                       └──Type expr: Variable: 10906
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Push
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: 10944
                                                                └──Type expr: Variable: 10942
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: 10906
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: 10944
                                                             └──Type expr: Variable: 10942
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: 10944
                                                                └──Desc: Any
                                                             └──Pattern:
                                                                └──Type expr: Variable: 10942
                                                                └──Desc: Variable: v
                                           └──Expression:
                                              └──Type expr: Variable: 10907
                                              └──Desc: Variable
                                                 └──Variable: v
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: 10906
                                                    └──Type expr: Variable: 10907
                                                 └──Type expr: Constructor: stack
                                                    └──Type expr: Variable: 10906
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: 10906
                                                       └──Type expr: Variable: 10907
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: 10982
                                                                └──Type expr: Variable: 10907
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: 10906
                                                                └──Type expr: Variable: 10907
                                                       └──Pattern:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: 10982
                                                             └──Type expr: Variable: 10907
                                                          └──Desc: Variable: ix
                                                 └──Pattern:
                                                    └──Type expr: Constructor: stack
                                                       └──Type expr: Variable: 10906
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Push
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: 10979
                                                                └──Type expr: Variable: 10977
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: 10906
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: 10979
                                                             └──Type expr: Variable: 10977
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: 10979
                                                                └──Desc: Variable: s
                                                             └──Pattern:
                                                                └──Type expr: Variable: 10977
                                                                └──Desc: Any
                                           └──Expression:
                                              └──Type expr: Variable: 10907
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: stack
                                                          └──Type expr: Variable: 10979
                                                       └──Type expr: Variable: 10907
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: 10979
                                                                └──Type expr: Variable: 10907
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: 10979
                                                                └──Type expr: Variable: 10907
                                                          └──Desc: Variable
                                                             └──Variable: prj
                                                             └──Type expr: Variable: 10907
                                                             └──Type expr: Variable: 10979
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: 10979
                                                             └──Type expr: Variable: 10907
                                                          └──Desc: Variable
                                                             └──Variable: ix
                                                 └──Expression:
                                                    └──Type expr: Constructor: stack
                                                       └──Type expr: Variable: 10979
                                                    └──Desc: Variable
                                                       └──Variable: s
       └──Structure item: Type
          └──Type declaration:
             └──Type name: dterm
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: D_var
                   └──Constructor alphas: 10102 10103
                   └──Constructor type:
                      └──Type expr: Constructor: dterm
                         └──Type expr: Variable: 10102
                         └──Type expr: Variable: 10103
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: index
                         └──Type expr: Variable: 10102
                         └──Type expr: Variable: 10103
                └──Constructor declaration:
                   └──Constructor name: D_con
                   └──Constructor alphas: 10102 10103
                   └──Constructor type:
                      └──Type expr: Constructor: dterm
                         └──Type expr: Variable: 10102
                         └──Type expr: Variable: 10103
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: 10103
                └──Constructor declaration:
                   └──Constructor name: D_lam
                   └──Constructor alphas: 10102 10103
                   └──Constructor type:
                      └──Type expr: Constructor: dterm
                         └──Type expr: Variable: 10102
                         └──Type expr: Variable: 10103
                   └──Constructor argument:
                      └──Constructor betas: 10108 10107
                      └──Type expr: Constructor: dterm
                         └──Type expr: Tuple
                            └──Type expr: Variable: 10102
                            └──Type expr: Variable: 10107
                         └──Type expr: Variable: 10108
                   └──Constraint:
                      └──Type expr: Variable: 10103
                      └──Type expr: Arrow
                         └──Type expr: Variable: 10107
                         └──Type expr: Variable: 10108
                └──Constructor declaration:
                   └──Constructor name: D_app
                   └──Constructor alphas: 10102 10103
                   └──Constructor type:
                      └──Type expr: Constructor: dterm
                         └──Type expr: Variable: 10102
                         └──Type expr: Variable: 10103
                   └──Constructor argument:
                      └──Constructor betas: 10113
                      └──Type expr: Tuple
                         └──Type expr: Constructor: dterm
                            └──Type expr: Variable: 10102
                            └──Type expr: Arrow
                               └──Type expr: Variable: 10113
                               └──Type expr: Variable: 10103
                         └──Type expr: Constructor: dterm
                            └──Type expr: Variable: 10102
                            └──Type expr: Variable: 10113
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: deval
                └──Abstraction:
                   └──Variables: 11027,11026
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: dterm
                            └──Type expr: Variable: 11052
                            └──Type expr: Variable: 11053
                         └──Type expr: Arrow
                            └──Type expr: Constructor: stack
                               └──Type expr: Variable: 11052
                            └──Type expr: Variable: 11053
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: dterm
                               └──Type expr: Variable: 11052
                               └──Type expr: Variable: 11053
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: stack
                                  └──Type expr: Variable: 11052
                               └──Type expr: Variable: 11053
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: stack
                                     └──Type expr: Variable: 11052
                                  └──Desc: Variable: s
                               └──Expression:
                                  └──Type expr: Variable: 11053
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: dterm
                                           └──Type expr: Variable: 11052
                                           └──Type expr: Variable: 11053
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Constructor: dterm
                                        └──Type expr: Variable: 11052
                                        └──Type expr: Variable: 11053
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: 11052
                                                 └──Type expr: Variable: 11053
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: index
                                                          └──Type expr: Variable: 11052
                                                          └──Type expr: Variable: 11053
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: 11052
                                                          └──Type expr: Variable: 11053
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: 11052
                                                       └──Type expr: Variable: 11053
                                                    └──Desc: Variable: ix
                                           └──Expression:
                                              └──Type expr: Variable: 11053
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: stack
                                                          └──Type expr: Variable: 11052
                                                       └──Type expr: Variable: 11053
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: 11052
                                                                └──Type expr: Variable: 11053
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: 11052
                                                                └──Type expr: Variable: 11053
                                                          └──Desc: Variable
                                                             └──Variable: prj
                                                             └──Type expr: Variable: 11053
                                                             └──Type expr: Variable: 11052
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: 11052
                                                             └──Type expr: Variable: 11053
                                                          └──Desc: Variable
                                                             └──Variable: ix
                                                 └──Expression:
                                                    └──Type expr: Constructor: stack
                                                       └──Type expr: Variable: 11052
                                                    └──Desc: Variable
                                                       └──Variable: s
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: 11052
                                                 └──Type expr: Variable: 11053
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_con
                                                    └──Constructor argument type:
                                                       └──Type expr: Variable: 11053
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: 11052
                                                          └──Type expr: Variable: 11053
                                                 └──Pattern:
                                                    └──Type expr: Variable: 11053
                                                    └──Desc: Variable: v
                                           └──Expression:
                                              └──Type expr: Variable: 11053
                                              └──Desc: Variable
                                                 └──Variable: v
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: 11052
                                                 └──Type expr: Variable: 11053
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_lam
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 11052
                                                             └──Type expr: Variable: 11110
                                                          └──Type expr: Variable: 11108
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: 11052
                                                          └──Type expr: Variable: 11053
                                                 └──Pattern:
                                                    └──Type expr: Constructor: dterm
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 11052
                                                          └──Type expr: Variable: 11110
                                                       └──Type expr: Variable: 11108
                                                    └──Desc: Variable: b
                                           └──Expression:
                                              └──Type expr: Variable: 11053
                                              └──Desc: Function
                                                 └──Pattern:
                                                    └──Type expr: Variable: 11110
                                                    └──Desc: Variable: x
                                                 └──Expression:
                                                    └──Type expr: Variable: 11108
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 11052
                                                                   └──Type expr: Variable: 11110
                                                             └──Type expr: Variable: 11108
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 11052
                                                                         └──Type expr: Variable: 11110
                                                                      └──Type expr: Variable: 11108
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 11052
                                                                            └──Type expr: Variable: 11110
                                                                      └──Type expr: Variable: 11108
                                                                └──Desc: Variable
                                                                   └──Variable: deval
                                                                   └──Type expr: Variable: 11108
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 11052
                                                                      └──Type expr: Variable: 11110
                                                             └──Expression:
                                                                └──Type expr: Constructor: dterm
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 11052
                                                                      └──Type expr: Variable: 11110
                                                                   └──Type expr: Variable: 11108
                                                                └──Desc: Variable
                                                                   └──Variable: b
                                                       └──Expression:
                                                          └──Type expr: Constructor: stack
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 11052
                                                                └──Type expr: Variable: 11110
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Push
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Variable: 11052
                                                                      └──Type expr: Variable: 11110
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: stack
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 11052
                                                                         └──Type expr: Variable: 11110
                                                             └──Expression:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: stack
                                                                      └──Type expr: Variable: 11052
                                                                   └──Type expr: Variable: 11110
                                                                └──Desc: Tuple
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Variable: 11052
                                                                      └──Desc: Variable
                                                                         └──Variable: s
                                                                   └──Expression:
                                                                      └──Type expr: Variable: 11110
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: 11052
                                                 └──Type expr: Variable: 11053
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_app
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: 11052
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: 11173
                                                                └──Type expr: Variable: 11053
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: 11052
                                                             └──Type expr: Variable: 11173
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: 11052
                                                          └──Type expr: Variable: 11053
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: 11052
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 11173
                                                             └──Type expr: Variable: 11053
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: 11052
                                                          └──Type expr: Variable: 11173
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: 11052
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: 11173
                                                                └──Type expr: Variable: 11053
                                                          └──Desc: Variable: f
                                                       └──Pattern:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: 11052
                                                             └──Type expr: Variable: 11173
                                                          └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Variable: 11053
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 11173
                                                       └──Type expr: Variable: 11053
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: 11052
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: 11173
                                                                └──Type expr: Variable: 11053
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Variable: 11052
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: 11173
                                                                         └──Type expr: Variable: 11053
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Variable: 11052
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: 11173
                                                                         └──Type expr: Variable: 11053
                                                                └──Desc: Variable
                                                                   └──Variable: deval
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: 11173
                                                                      └──Type expr: Variable: 11053
                                                                   └──Type expr: Variable: 11052
                                                             └──Expression:
                                                                └──Type expr: Constructor: dterm
                                                                   └──Type expr: Variable: 11052
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: 11173
                                                                      └──Type expr: Variable: 11053
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Constructor: stack
                                                             └──Type expr: Variable: 11052
                                                          └──Desc: Variable
                                                             └──Variable: s
                                                 └──Expression:
                                                    └──Type expr: Variable: 11173
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: 11052
                                                             └──Type expr: Variable: 11173
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Variable: 11052
                                                                      └──Type expr: Variable: 11173
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Variable: 11052
                                                                      └──Type expr: Variable: 11173
                                                                └──Desc: Variable
                                                                   └──Variable: deval
                                                                   └──Type expr: Variable: 11173
                                                                   └──Type expr: Variable: 11052
                                                             └──Expression:
                                                                └──Type expr: Constructor: dterm
                                                                   └──Type expr: Variable: 11052
                                                                   └──Type expr: Variable: 11173
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: stack
                                                             └──Type expr: Variable: 11052
                                                          └──Desc: Variable
                                                             └──Variable: s
       └──Structure item: Type
          └──Type declaration:
             └──Type name: layout
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Empty_layout
                   └──Constructor alphas: 10119 10120
                   └──Constructor type:
                      └──Type expr: Constructor: layout
                         └──Type expr: Variable: 10119
                         └──Type expr: Variable: 10120
                   └──Constraint:
                      └──Type expr: Variable: 10120
                      └──Type expr: Constructor: unit
                └──Constructor declaration:
                   └──Constructor name: Push_layout
                   └──Constructor alphas: 10119 10120
                   └──Constructor type:
                      └──Type expr: Constructor: layout
                         └──Type expr: Variable: 10119
                         └──Type expr: Variable: 10120
                   └──Constructor argument:
                      └──Constructor betas: 10124 10123
                      └──Type expr: Tuple
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 10123
                         └──Type expr: Constructor: layout
                            └──Type expr: Variable: 10119
                            └──Type expr: Variable: 10124
                         └──Type expr: Constructor: index
                            └──Type expr: Variable: 10119
                            └──Type expr: Variable: 10123
                   └──Constraint:
                      └──Type expr: Variable: 10120
                      └──Type expr: Tuple
                         └──Type expr: Variable: 10124
                         └──Type expr: Variable: 10123
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: size
                └──Abstraction:
                   └──Variables: 11227,11226
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: layout
                            └──Type expr: Variable: 11248
                            └──Type expr: Variable: 11249
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: layout
                               └──Type expr: Variable: 11248
                               └──Type expr: Variable: 11249
                            └──Desc: Variable: l
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: layout
                                     └──Type expr: Variable: 11248
                                     └──Type expr: Variable: 11249
                                  └──Desc: Variable
                                     └──Variable: l
                               └──Type expr: Constructor: layout
                                  └──Type expr: Variable: 11248
                                  └──Type expr: Variable: 11249
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: 11248
                                           └──Type expr: Variable: 11249
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Empty_layout
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: 11248
                                                    └──Type expr: Variable: 11249
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 0
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: 11248
                                           └──Type expr: Variable: 11249
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Push_layout
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 11284
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: 11248
                                                       └──Type expr: Variable: 11282
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: 11248
                                                       └──Type expr: Variable: 11284
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: 11248
                                                    └──Type expr: Variable: 11249
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 11284
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: 11248
                                                    └──Type expr: Variable: 11282
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: 11248
                                                    └──Type expr: Variable: 11284
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 11284
                                                    └──Desc: Any
                                                 └──Pattern:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: 11248
                                                       └──Type expr: Variable: 11282
                                                    └──Desc: Variable: l
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: 11248
                                                       └──Type expr: Variable: 11284
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
                                                                └──Type expr: Variable: 11248
                                                                └──Type expr: Variable: 11282
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: size
                                                             └──Type expr: Variable: 11282
                                                             └──Type expr: Variable: 11248
                                                       └──Expression:
                                                          └──Type expr: Constructor: layout
                                                             └──Type expr: Variable: 11248
                                                             └──Type expr: Variable: 11282
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
                   └──Variables: 11333,11336,11335
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: layout
                            └──Type expr: Variable: 11363
                            └──Type expr: Variable: 11364
                         └──Type expr: Constructor: layout
                            └──Type expr: Tuple
                               └──Type expr: Variable: 11363
                               └──Type expr: Variable: 11395
                            └──Type expr: Variable: 11364
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: layout
                               └──Type expr: Variable: 11363
                               └──Type expr: Variable: 11364
                            └──Desc: Variable: l
                         └──Expression:
                            └──Type expr: Constructor: layout
                               └──Type expr: Tuple
                                  └──Type expr: Variable: 11363
                                  └──Type expr: Variable: 11395
                               └──Type expr: Variable: 11364
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: layout
                                     └──Type expr: Variable: 11363
                                     └──Type expr: Variable: 11364
                                  └──Desc: Variable
                                     └──Variable: l
                               └──Type expr: Constructor: layout
                                  └──Type expr: Variable: 11363
                                  └──Type expr: Variable: 11364
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: 11363
                                           └──Type expr: Variable: 11364
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Empty_layout
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: 11363
                                                    └──Type expr: Variable: 11364
                                     └──Expression:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 11363
                                              └──Type expr: Variable: 11395
                                           └──Type expr: Variable: 11364
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Empty_layout
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 11363
                                                       └──Type expr: Variable: 11395
                                                    └──Type expr: Variable: 11364
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: 11363
                                           └──Type expr: Variable: 11364
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Push_layout
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 11425
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: 11363
                                                       └──Type expr: Variable: 11423
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: 11363
                                                       └──Type expr: Variable: 11425
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: 11363
                                                    └──Type expr: Variable: 11364
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 11425
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: 11363
                                                    └──Type expr: Variable: 11423
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: 11363
                                                    └──Type expr: Variable: 11425
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 11425
                                                    └──Desc: Variable: t
                                                 └──Pattern:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: 11363
                                                       └──Type expr: Variable: 11423
                                                    └──Desc: Variable: l
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: 11363
                                                       └──Type expr: Variable: 11425
                                                    └──Desc: Variable: ix
                                     └──Expression:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 11363
                                              └──Type expr: Variable: 11395
                                           └──Type expr: Variable: 11364
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Push_layout
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 11425
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 11363
                                                          └──Type expr: Variable: 11395
                                                       └──Type expr: Variable: 11423
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 11363
                                                          └──Type expr: Variable: 11395
                                                       └──Type expr: Variable: 11425
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 11363
                                                       └──Type expr: Variable: 11395
                                                    └──Type expr: Variable: 11364
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: 11425
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 11363
                                                       └──Type expr: Variable: 11395
                                                    └──Type expr: Variable: 11423
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 11363
                                                       └──Type expr: Variable: 11395
                                                    └──Type expr: Variable: 11425
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: 11425
                                                    └──Desc: Variable
                                                       └──Variable: t
                                                 └──Expression:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 11363
                                                          └──Type expr: Variable: 11395
                                                       └──Type expr: Variable: 11423
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: 11363
                                                                └──Type expr: Variable: 11423
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 11363
                                                                   └──Type expr: Variable: 11395
                                                                └──Type expr: Variable: 11423
                                                          └──Desc: Variable
                                                             └──Variable: inc
                                                             └──Type expr: Variable: 11395
                                                             └──Type expr: Variable: 11423
                                                             └──Type expr: Variable: 11363
                                                       └──Expression:
                                                          └──Type expr: Constructor: layout
                                                             └──Type expr: Variable: 11363
                                                             └──Type expr: Variable: 11423
                                                          └──Desc: Variable
                                                             └──Variable: l
                                                 └──Expression:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 11363
                                                          └──Type expr: Variable: 11395
                                                       └──Type expr: Variable: 11425
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: 11363
                                                                └──Type expr: Variable: 11425
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 11363
                                                                   └──Type expr: Variable: 11395
                                                                └──Type expr: Variable: 11425
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: 11363
                                                             └──Type expr: Variable: 11425
                                                          └──Desc: Variable
                                                             └──Variable: ix
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: prjl
                └──Abstraction:
                   └──Variables: 11514,11513,11517
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: 11549
                         └──Type expr: Arrow
                            └──Type expr: Constructor: int
                            └──Type expr: Arrow
                               └──Type expr: Constructor: layout
                                  └──Type expr: Variable: 11568
                                  └──Type expr: Variable: 11569
                               └──Type expr: Constructor: index
                                  └──Type expr: Variable: 11568
                                  └──Type expr: Variable: 11549
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: 11549
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: layout
                                     └──Type expr: Variable: 11568
                                     └──Type expr: Variable: 11569
                                  └──Type expr: Constructor: index
                                     └──Type expr: Variable: 11568
                                     └──Type expr: Variable: 11549
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable: n
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: layout
                                        └──Type expr: Variable: 11568
                                        └──Type expr: Variable: 11569
                                     └──Type expr: Constructor: index
                                        └──Type expr: Variable: 11568
                                        └──Type expr: Variable: 11549
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: 11568
                                           └──Type expr: Variable: 11569
                                        └──Desc: Variable: l
                                     └──Expression:
                                        └──Type expr: Constructor: index
                                           └──Type expr: Variable: 11568
                                           └──Type expr: Variable: 11549
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: layout
                                                 └──Type expr: Variable: 11568
                                                 └──Type expr: Variable: 11569
                                              └──Desc: Variable
                                                 └──Variable: l
                                           └──Type expr: Constructor: layout
                                              └──Type expr: Variable: 11568
                                              └──Type expr: Variable: 11569
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: 11568
                                                       └──Type expr: Variable: 11569
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Empty_layout
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: 11568
                                                                └──Type expr: Variable: 11569
                                                 └──Expression:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: 11568
                                                       └──Type expr: Variable: 11549
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: string
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: 11568
                                                                └──Type expr: Variable: 11549
                                                          └──Desc: Variable
                                                             └──Variable: fail_with
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: 11568
                                                                └──Type expr: Variable: 11549
                                                       └──Expression:
                                                          └──Type expr: Constructor: string
                                                          └──Desc: Constant: convert prjl
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: 11568
                                                       └──Type expr: Variable: 11569
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Push_layout
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 11618
                                                                └──Type expr: Constructor: layout
                                                                   └──Type expr: Variable: 11568
                                                                   └──Type expr: Variable: 11616
                                                                └──Type expr: Constructor: index
                                                                   └──Type expr: Variable: 11568
                                                                   └──Type expr: Variable: 11618
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: 11568
                                                                └──Type expr: Variable: 11569
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: 11618
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: 11568
                                                                └──Type expr: Variable: 11616
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: 11568
                                                                └──Type expr: Variable: 11618
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: 11618
                                                                └──Desc: Variable: t'
                                                             └──Pattern:
                                                                └──Type expr: Constructor: layout
                                                                   └──Type expr: Variable: 11568
                                                                   └──Type expr: Variable: 11616
                                                                └──Desc: Variable: l
                                                             └──Pattern:
                                                                └──Type expr: Constructor: index
                                                                   └──Type expr: Variable: 11568
                                                                   └──Type expr: Variable: 11618
                                                                └──Desc: Variable: ix
                                                 └──Expression:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: 11568
                                                       └──Type expr: Variable: 11549
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
                                                             └──Type expr: Variable: 11568
                                                             └──Type expr: Variable: 11549
                                                          └──Desc: Match
                                                             └──Expression:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: 11549
                                                                   └──Type expr: Variable: 11618
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: 11618
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: 11549
                                                                            └──Type expr: Variable: 11618
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: ty
                                                                                  └──Type expr: Variable: 11549
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: ty
                                                                                     └──Type expr: Variable: 11618
                                                                                  └──Type expr: Constructor: eq
                                                                                     └──Type expr: Variable: 11549
                                                                                     └──Type expr: Variable: 11618
                                                                            └──Desc: Variable
                                                                               └──Variable: check_eq
                                                                               └──Type expr: Variable: 11618
                                                                               └──Type expr: Variable: 11549
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: 11549
                                                                            └──Desc: Variable
                                                                               └──Variable: t
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: 11618
                                                                      └──Desc: Variable
                                                                         └──Variable: t'
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: 11549
                                                                └──Type expr: Variable: 11618
                                                             └──Cases:
                                                                └──Case:
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: eq
                                                                         └──Type expr: Variable: 11549
                                                                         └──Type expr: Variable: 11618
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Refl
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: eq
                                                                                  └──Type expr: Variable: 11549
                                                                                  └──Type expr: Variable: 11618
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: index
                                                                         └──Type expr: Variable: 11568
                                                                         └──Type expr: Variable: 11549
                                                                      └──Desc: Variable
                                                                         └──Variable: ix
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: 11568
                                                             └──Type expr: Variable: 11549
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: layout
                                                                      └──Type expr: Variable: 11568
                                                                      └──Type expr: Variable: 11616
                                                                   └──Type expr: Constructor: index
                                                                      └──Type expr: Variable: 11568
                                                                      └──Type expr: Variable: 11549
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: int
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: layout
                                                                               └──Type expr: Variable: 11568
                                                                               └──Type expr: Variable: 11616
                                                                            └──Type expr: Constructor: index
                                                                               └──Type expr: Variable: 11568
                                                                               └──Type expr: Variable: 11549
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: ty
                                                                                  └──Type expr: Variable: 11549
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: int
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: layout
                                                                                        └──Type expr: Variable: 11568
                                                                                        └──Type expr: Variable: 11616
                                                                                     └──Type expr: Constructor: index
                                                                                        └──Type expr: Variable: 11568
                                                                                        └──Type expr: Variable: 11549
                                                                            └──Desc: Variable
                                                                               └──Variable: prjl
                                                                               └──Type expr: Variable: 11616
                                                                               └──Type expr: Variable: 11568
                                                                               └──Type expr: Variable: 11549
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: 11549
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
                                                                   └──Type expr: Variable: 11568
                                                                   └──Type expr: Variable: 11616
                                                                └──Desc: Variable
                                                                   └──Variable: l
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: convert
                └──Abstraction:
                   └──Variables: 11743,11746
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: layout
                            └──Type expr: Variable: 11775
                            └──Type expr: Variable: 11775
                         └──Type expr: Arrow
                            └──Type expr: Constructor: hterm
                               └──Type expr: Variable: 11785
                            └──Type expr: Constructor: dterm
                               └──Type expr: Variable: 11775
                               └──Type expr: Variable: 11785
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: layout
                               └──Type expr: Variable: 11775
                               └──Type expr: Variable: 11775
                            └──Desc: Variable: l
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: hterm
                                  └──Type expr: Variable: 11785
                               └──Type expr: Constructor: dterm
                                  └──Type expr: Variable: 11775
                                  └──Type expr: Variable: 11785
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: hterm
                                     └──Type expr: Variable: 11785
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Constructor: dterm
                                     └──Type expr: Variable: 11775
                                     └──Type expr: Variable: 11785
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: 11785
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Constructor: hterm
                                        └──Type expr: Variable: 11785
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: hterm
                                                 └──Type expr: Variable: 11785
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Tag
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: 11785
                                                          └──Type expr: Constructor: int
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: 11785
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: 11785
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: 11785
                                                          └──Desc: Variable: t
                                                       └──Pattern:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable: sz
                                           └──Expression:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: 11775
                                                 └──Type expr: Variable: 11785
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: index
                                                          └──Type expr: Variable: 11775
                                                          └──Type expr: Variable: 11785
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: 11775
                                                          └──Type expr: Variable: 11785
                                                 └──Expression:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: 11775
                                                       └──Type expr: Variable: 11785
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: 11775
                                                                └──Type expr: Variable: 11775
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: 11775
                                                                └──Type expr: Variable: 11785
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: int
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Variable: 11775
                                                                         └──Type expr: Variable: 11775
                                                                      └──Type expr: Constructor: index
                                                                         └──Type expr: Variable: 11775
                                                                         └──Type expr: Variable: 11785
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: 11785
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: int
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: layout
                                                                                  └──Type expr: Variable: 11775
                                                                                  └──Type expr: Variable: 11775
                                                                               └──Type expr: Constructor: index
                                                                                  └──Type expr: Variable: 11775
                                                                                  └──Type expr: Variable: 11785
                                                                      └──Desc: Variable
                                                                         └──Variable: prjl
                                                                         └──Type expr: Variable: 11775
                                                                         └──Type expr: Variable: 11775
                                                                         └──Type expr: Variable: 11785
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: 11785
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
                                                                                                    └──Type expr: Variable: 11775
                                                                                                    └──Type expr: Variable: 11775
                                                                                                 └──Type expr: Constructor: int
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: size
                                                                                                 └──Type expr: Variable: 11775
                                                                                                 └──Type expr: Variable: 11775
                                                                                           └──Expression:
                                                                                              └──Type expr: Constructor: layout
                                                                                                 └──Type expr: Variable: 11775
                                                                                                 └──Type expr: Variable: 11775
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
                                                             └──Type expr: Variable: 11775
                                                             └──Type expr: Variable: 11775
                                                          └──Desc: Variable
                                                             └──Variable: l
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: hterm
                                                 └──Type expr: Variable: 11785
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Con
                                                    └──Constructor argument type:
                                                       └──Type expr: Variable: 11785
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: 11785
                                                 └──Pattern:
                                                    └──Type expr: Variable: 11785
                                                    └──Desc: Variable: v
                                           └──Expression:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: 11775
                                                 └──Type expr: Variable: 11785
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_con
                                                    └──Constructor argument type:
                                                       └──Type expr: Variable: 11785
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: 11775
                                                          └──Type expr: Variable: 11785
                                                 └──Expression:
                                                    └──Type expr: Variable: 11785
                                                    └──Desc: Variable
                                                       └──Variable: v
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: hterm
                                                 └──Type expr: Variable: 11785
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Lam
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: 11924
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: 11924
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: 11920
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: 11785
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: 11924
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: 11924
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: 11920
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: 11924
                                                          └──Desc: Variable: t
                                                       └──Pattern:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: 11924
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: 11920
                                                          └──Desc: Variable: f
                                           └──Expression:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: 11775
                                                 └──Type expr: Variable: 11785
                                              └──Desc: Let
                                                 └──Value bindings:
                                                    └──Value binding:
                                                       └──Pattern:
                                                          └──Type expr: Constructor: layout
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 11775
                                                                └──Type expr: Variable: 11924
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 11775
                                                                └──Type expr: Variable: 11924
                                                          └──Desc: Variable: l'
                                                       └──Abstraction:
                                                          └──Variables:
                                                          └──Expression:
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 11775
                                                                   └──Type expr: Variable: 11924
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 11775
                                                                   └──Type expr: Variable: 11924
                                                             └──Desc: Construct
                                                                └──Constructor description:
                                                                   └──Name: Push_layout
                                                                   └──Constructor argument type:
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: 11924
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 11775
                                                                               └──Type expr: Variable: 11924
                                                                            └──Type expr: Variable: 11775
                                                                         └──Type expr: Constructor: index
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 11775
                                                                               └──Type expr: Variable: 11924
                                                                            └──Type expr: Variable: 11924
                                                                   └──Constructor type:
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 11775
                                                                            └──Type expr: Variable: 11924
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 11775
                                                                            └──Type expr: Variable: 11924
                                                                └──Expression:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: 11924
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 11775
                                                                            └──Type expr: Variable: 11924
                                                                         └──Type expr: Variable: 11775
                                                                      └──Type expr: Constructor: index
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 11775
                                                                            └──Type expr: Variable: 11924
                                                                         └──Type expr: Variable: 11924
                                                                   └──Desc: Tuple
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: 11924
                                                                         └──Desc: Variable
                                                                            └──Variable: t
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 11775
                                                                               └──Type expr: Variable: 11924
                                                                            └──Type expr: Variable: 11775
                                                                         └──Desc: Application
                                                                            └──Expression:
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: layout
                                                                                     └──Type expr: Variable: 11775
                                                                                     └──Type expr: Variable: 11775
                                                                                  └──Type expr: Constructor: layout
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Variable: 11775
                                                                                        └──Type expr: Variable: 11924
                                                                                     └──Type expr: Variable: 11775
                                                                               └──Desc: Variable
                                                                                  └──Variable: inc
                                                                                  └──Type expr: Variable: 11924
                                                                                  └──Type expr: Variable: 11775
                                                                                  └──Type expr: Variable: 11775
                                                                            └──Expression:
                                                                               └──Type expr: Constructor: layout
                                                                                  └──Type expr: Variable: 11775
                                                                                  └──Type expr: Variable: 11775
                                                                               └──Desc: Variable
                                                                                  └──Variable: l
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: index
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 11775
                                                                               └──Type expr: Variable: 11924
                                                                            └──Type expr: Variable: 11924
                                                                         └──Desc: Construct
                                                                            └──Constructor description:
                                                                               └──Name: Zero
                                                                               └──Constructor argument type:
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Constructor type:
                                                                                  └──Type expr: Constructor: index
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Variable: 11775
                                                                                        └──Type expr: Variable: 11924
                                                                                     └──Type expr: Variable: 11924
                                                                            └──Expression:
                                                                               └──Type expr: Constructor: unit
                                                                               └──Desc: Constant: ()
                                                 └──Expression:
                                                    └──Type expr: Constructor: dterm
                                                       └──Type expr: Variable: 11775
                                                       └──Type expr: Variable: 11785
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: D_lam
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: dterm
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 11775
                                                                   └──Type expr: Variable: 11924
                                                                └──Type expr: Variable: 11920
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: dterm
                                                                └──Type expr: Variable: 11775
                                                                └──Type expr: Variable: 11785
                                                       └──Expression:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 11775
                                                                └──Type expr: Variable: 11924
                                                             └──Type expr: Variable: 11920
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: hterm
                                                                      └──Type expr: Variable: 11920
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 11775
                                                                         └──Type expr: Variable: 11924
                                                                      └──Type expr: Variable: 11920
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 11775
                                                                               └──Type expr: Variable: 11924
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 11775
                                                                               └──Type expr: Variable: 11924
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: hterm
                                                                               └──Type expr: Variable: 11920
                                                                            └──Type expr: Constructor: dterm
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: 11775
                                                                                  └──Type expr: Variable: 11924
                                                                               └──Type expr: Variable: 11920
                                                                      └──Desc: Variable
                                                                         └──Variable: convert
                                                                         └──Type expr: Variable: 11920
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 11775
                                                                            └──Type expr: Variable: 11924
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 11775
                                                                            └──Type expr: Variable: 11924
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 11775
                                                                            └──Type expr: Variable: 11924
                                                                      └──Desc: Variable
                                                                         └──Variable: l'
                                                             └──Expression:
                                                                └──Type expr: Constructor: hterm
                                                                   └──Type expr: Variable: 11920
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: hterm
                                                                            └──Type expr: Variable: 11924
                                                                         └──Type expr: Constructor: hterm
                                                                            └──Type expr: Variable: 11920
                                                                      └──Desc: Variable
                                                                         └──Variable: f
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: hterm
                                                                         └──Type expr: Variable: 11924
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Tag
                                                                            └──Constructor argument type:
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Constructor: ty
                                                                                     └──Type expr: Variable: 11924
                                                                                  └──Type expr: Constructor: int
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: hterm
                                                                                  └──Type expr: Variable: 11924
                                                                         └──Expression:
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Constructor: ty
                                                                                  └──Type expr: Variable: 11924
                                                                               └──Type expr: Constructor: int
                                                                            └──Desc: Tuple
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: ty
                                                                                     └──Type expr: Variable: 11924
                                                                                  └──Desc: Variable
                                                                                     └──Variable: t
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: int
                                                                                  └──Desc: Application
                                                                                     └──Expression:
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Constructor: layout
                                                                                              └──Type expr: Variable: 11775
                                                                                              └──Type expr: Variable: 11775
                                                                                           └──Type expr: Constructor: int
                                                                                        └──Desc: Variable
                                                                                           └──Variable: size
                                                                                           └──Type expr: Variable: 11775
                                                                                           └──Type expr: Variable: 11775
                                                                                     └──Expression:
                                                                                        └──Type expr: Constructor: layout
                                                                                           └──Type expr: Variable: 11775
                                                                                           └──Type expr: Variable: 11775
                                                                                        └──Desc: Variable
                                                                                           └──Variable: l
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: hterm
                                                 └──Type expr: Variable: 11785
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: App
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: 12062
                                                                └──Type expr: Variable: 11785
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: 12062
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: 11785
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 12062
                                                             └──Type expr: Variable: 11785
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: 12062
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: 12062
                                                                └──Type expr: Variable: 11785
                                                          └──Desc: Variable: f
                                                       └──Pattern:
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: 12062
                                                          └──Desc: Variable: a
                                           └──Expression:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: 11775
                                                 └──Type expr: Variable: 11785
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_app
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: 11775
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: 12062
                                                                └──Type expr: Variable: 11785
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: 11775
                                                             └──Type expr: Variable: 12062
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: 11775
                                                          └──Type expr: Variable: 11785
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: 11775
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 12062
                                                             └──Type expr: Variable: 11785
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: 11775
                                                          └──Type expr: Variable: 12062
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: 11775
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: 12062
                                                                └──Type expr: Variable: 11785
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: hterm
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: 12062
                                                                         └──Type expr: Variable: 11785
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Variable: 11775
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: 12062
                                                                         └──Type expr: Variable: 11785
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Variable: 11775
                                                                            └──Type expr: Variable: 11775
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: hterm
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: 12062
                                                                                  └──Type expr: Variable: 11785
                                                                            └──Type expr: Constructor: dterm
                                                                               └──Type expr: Variable: 11775
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: 12062
                                                                                  └──Type expr: Variable: 11785
                                                                      └──Desc: Variable
                                                                         └──Variable: convert
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Variable: 12062
                                                                            └──Type expr: Variable: 11785
                                                                         └──Type expr: Variable: 11775
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Variable: 11775
                                                                         └──Type expr: Variable: 11775
                                                                      └──Desc: Variable
                                                                         └──Variable: l
                                                             └──Expression:
                                                                └──Type expr: Constructor: hterm
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: 12062
                                                                      └──Type expr: Variable: 11785
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: 11775
                                                             └──Type expr: Variable: 12062
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: hterm
                                                                      └──Type expr: Variable: 12062
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Variable: 11775
                                                                      └──Type expr: Variable: 12062
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Variable: 11775
                                                                            └──Type expr: Variable: 11775
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: hterm
                                                                               └──Type expr: Variable: 12062
                                                                            └──Type expr: Constructor: dterm
                                                                               └──Type expr: Variable: 11775
                                                                               └──Type expr: Variable: 12062
                                                                      └──Desc: Variable
                                                                         └──Variable: convert
                                                                         └──Type expr: Variable: 12062
                                                                         └──Type expr: Variable: 11775
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Variable: 11775
                                                                         └──Type expr: Variable: 11775
                                                                      └──Desc: Variable
                                                                         └──Variable: l
                                                             └──Expression:
                                                                └──Type expr: Constructor: hterm
                                                                   └──Type expr: Variable: 12062
                                                                └──Desc: Variable
                                                                   └──Variable: a |}]