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
                   └──Variables: a9807,a9809
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: a9835
                         └──Type expr: Arrow
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: a9845
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: a9835
                               └──Type expr: Variable: a9845
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: a9835
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: ty
                                  └──Type expr: Variable: a9845
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: a9835
                                  └──Type expr: Variable: a9845
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: ty
                                     └──Type expr: Variable: a9845
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: a9835
                                     └──Type expr: Variable: a9845
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: ty
                                              └──Type expr: Variable: a9835
                                           └──Type expr: Constructor: ty
                                              └──Type expr: Variable: a9845
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: a9835
                                              └──Desc: Variable
                                                 └──Variable: t1
                                           └──Expression:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: a9845
                                              └──Desc: Variable
                                                 └──Variable: t2
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: ty
                                           └──Type expr: Variable: a9835
                                        └──Type expr: Constructor: ty
                                           └──Type expr: Variable: a9845
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a9835
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a9845
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a9835
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a9835
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a9845
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a9845
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a9835
                                                 └──Type expr: Variable: a9845
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Refl
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a9835
                                                          └──Type expr: Variable: a9835
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a9835
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a9845
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a9835
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: String
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a9835
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a9845
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: String
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a9845
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a9835
                                                 └──Type expr: Variable: a9845
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Refl
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a9835
                                                          └──Type expr: Variable: a9835
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a9835
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a9845
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a9835
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: List
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a9927
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a9835
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a9927
                                                          └──Desc: Variable: t1
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a9845
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: List
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a9924
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a9845
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a9924
                                                          └──Desc: Variable: t2
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a9835
                                                 └──Type expr: Variable: a9845
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a9927
                                                       └──Type expr: Variable: a9924
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a9924
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a9927
                                                                └──Type expr: Variable: a9924
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: a9927
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a9924
                                                                      └──Type expr: Constructor: eq
                                                                         └──Type expr: Variable: a9927
                                                                         └──Type expr: Variable: a9924
                                                                └──Desc: Variable
                                                                   └──Variable: check_eq
                                                                   └──Type expr: Variable: a9924
                                                                   └──Type expr: Variable: a9927
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a9927
                                                                └──Desc: Variable
                                                                   └──Variable: t1
                                                       └──Expression:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a9924
                                                          └──Desc: Variable
                                                             └──Variable: t2
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: a9927
                                                    └──Type expr: Variable: a9924
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a9927
                                                             └──Type expr: Variable: a9924
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Refl
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a9927
                                                                      └──Type expr: Variable: a9924
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a9835
                                                             └──Type expr: Variable: a9845
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Refl
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a9835
                                                                      └──Type expr: Variable: a9835
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a9835
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a9845
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a9835
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Pair
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a10009
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a10007
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a9835
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a10009
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a10007
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a10009
                                                                └──Desc: Variable: t11
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a10007
                                                                └──Desc: Variable: t12
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a9845
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Pair
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a10003
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a10001
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a9845
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a10003
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a10001
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a10003
                                                                └──Desc: Variable: t21
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a10001
                                                                └──Desc: Variable: t22
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a9835
                                                 └──Type expr: Variable: a9845
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a10009
                                                          └──Type expr: Variable: a10003
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a10007
                                                          └──Type expr: Variable: a10001
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a10009
                                                             └──Type expr: Variable: a10003
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: a10003
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a10009
                                                                      └──Type expr: Variable: a10003
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a10009
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: a10003
                                                                            └──Type expr: Constructor: eq
                                                                               └──Type expr: Variable: a10009
                                                                               └──Type expr: Variable: a10003
                                                                      └──Desc: Variable
                                                                         └──Variable: check_eq
                                                                         └──Type expr: Variable: a10003
                                                                         └──Type expr: Variable: a10009
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a10009
                                                                      └──Desc: Variable
                                                                         └──Variable: t11
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a10003
                                                                └──Desc: Variable
                                                                   └──Variable: t21
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a10007
                                                             └──Type expr: Variable: a10001
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: a10001
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a10007
                                                                      └──Type expr: Variable: a10001
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a10007
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: a10001
                                                                            └──Type expr: Constructor: eq
                                                                               └──Type expr: Variable: a10007
                                                                               └──Type expr: Variable: a10001
                                                                      └──Desc: Variable
                                                                         └──Variable: check_eq
                                                                         └──Type expr: Variable: a10001
                                                                         └──Type expr: Variable: a10007
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a10007
                                                                      └──Desc: Variable
                                                                         └──Variable: t12
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a10001
                                                                └──Desc: Variable
                                                                   └──Variable: t22
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a10009
                                                       └──Type expr: Variable: a10003
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a10007
                                                       └──Type expr: Variable: a10001
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a10009
                                                                └──Type expr: Variable: a10003
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a10007
                                                                └──Type expr: Variable: a10001
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: a10009
                                                                   └──Type expr: Variable: a10003
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: a10009
                                                                            └──Type expr: Variable: a10003
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: a10007
                                                                   └──Type expr: Variable: a10001
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: a10007
                                                                            └──Type expr: Variable: a10001
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a9835
                                                             └──Type expr: Variable: a9845
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Refl
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a9835
                                                                      └──Type expr: Variable: a9835
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a9835
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a9845
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a9835
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fun
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a10130
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a10128
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a9835
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a10130
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a10128
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a10130
                                                                └──Desc: Variable: t11
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a10128
                                                                └──Desc: Variable: t12
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a9845
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fun
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a10124
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a10122
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a9845
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a10124
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a10122
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a10124
                                                                └──Desc: Variable: t21
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a10122
                                                                └──Desc: Variable: t22
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a9835
                                                 └──Type expr: Variable: a9845
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a10130
                                                          └──Type expr: Variable: a10124
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a10128
                                                          └──Type expr: Variable: a10122
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a10130
                                                             └──Type expr: Variable: a10124
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: a10124
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a10130
                                                                      └──Type expr: Variable: a10124
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a10130
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: a10124
                                                                            └──Type expr: Constructor: eq
                                                                               └──Type expr: Variable: a10130
                                                                               └──Type expr: Variable: a10124
                                                                      └──Desc: Variable
                                                                         └──Variable: check_eq
                                                                         └──Type expr: Variable: a10124
                                                                         └──Type expr: Variable: a10130
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a10130
                                                                      └──Desc: Variable
                                                                         └──Variable: t11
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a10124
                                                                └──Desc: Variable
                                                                   └──Variable: t21
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a10128
                                                             └──Type expr: Variable: a10122
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: a10122
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a10128
                                                                      └──Type expr: Variable: a10122
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a10128
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: a10122
                                                                            └──Type expr: Constructor: eq
                                                                               └──Type expr: Variable: a10128
                                                                               └──Type expr: Variable: a10122
                                                                      └──Desc: Variable
                                                                         └──Variable: check_eq
                                                                         └──Type expr: Variable: a10122
                                                                         └──Type expr: Variable: a10128
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a10128
                                                                      └──Desc: Variable
                                                                         └──Variable: t12
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a10122
                                                                └──Desc: Variable
                                                                   └──Variable: t22
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a10130
                                                       └──Type expr: Variable: a10124
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a10128
                                                       └──Type expr: Variable: a10122
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a10130
                                                                └──Type expr: Variable: a10124
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a10128
                                                                └──Type expr: Variable: a10122
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: a10130
                                                                   └──Type expr: Variable: a10124
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: a10130
                                                                            └──Type expr: Variable: a10124
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: a10128
                                                                   └──Type expr: Variable: a10122
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: a10128
                                                                            └──Type expr: Variable: a10122
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a9835
                                                             └──Type expr: Variable: a9845
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Refl
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a9835
                                                                      └──Type expr: Variable: a9835
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: a10237
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: a10247
                         └──Type expr: Arrow
                            └──Type expr: Variable: a10237
                            └──Type expr: Variable: a10247
                   └──Desc: Variable: cast
                └──Abstraction:
                   └──Variables: a10237,a10247
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: a10237
                         └──Type expr: Arrow
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: a10247
                            └──Type expr: Arrow
                               └──Type expr: Variable: a10237
                               └──Type expr: Variable: a10247
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: a10237
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: ty
                                  └──Type expr: Variable: a10247
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a10237
                                  └──Type expr: Variable: a10247
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: ty
                                     └──Type expr: Variable: a10247
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a10237
                                     └──Type expr: Variable: a10247
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: a10237
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: a10247
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a10237
                                                 └──Type expr: Variable: a10247
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: a10247
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a10237
                                                          └──Type expr: Variable: a10247
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a10237
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a10247
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: a10237
                                                                   └──Type expr: Variable: a10247
                                                          └──Desc: Variable
                                                             └──Variable: check_eq
                                                             └──Type expr: Variable: a10247
                                                             └──Type expr: Variable: a10237
                                                       └──Expression:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a10237
                                                          └──Desc: Variable
                                                             └──Variable: t1
                                                 └──Expression:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a10247
                                                    └──Desc: Variable
                                                       └──Variable: t2
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: a10237
                                              └──Type expr: Variable: a10247
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a10237
                                                       └──Type expr: Variable: a10247
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Refl
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a10237
                                                                └──Type expr: Variable: a10247
                                                 └──Expression:
                                                    └──Type expr: Variable: a10247
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
                └──Variables: a10287
                └──Type expr: Arrow
                   └──Type expr: Constructor: string
                   └──Type expr: Variable: a10287
             └──Primitive name: %fail_with
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: heval
                └──Abstraction:
                   └──Variables: a10296
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: hterm
                            └──Type expr: Variable: a10313
                         └──Type expr: Variable: a10313
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: hterm
                               └──Type expr: Variable: a10313
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Variable: a10313
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: hterm
                                     └──Type expr: Variable: a10313
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: hterm
                                  └──Type expr: Variable: a10313
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: a10313
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Tag
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a10313
                                                    └──Type expr: Constructor: int
                                              └──Constructor type:
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: a10313
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a10313
                                                 └──Type expr: Constructor: int
                                              └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Variable: a10313
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: string
                                                 └──Type expr: Variable: a10313
                                              └──Desc: Variable
                                                 └──Variable: fail_with
                                                 └──Type expr: Variable: a10313
                                           └──Expression:
                                              └──Type expr: Constructor: string
                                              └──Desc: Constant: HOAS eval
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: a10313
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Con
                                              └──Constructor argument type:
                                                 └──Type expr: Variable: a10313
                                              └──Constructor type:
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: a10313
                                           └──Pattern:
                                              └──Type expr: Variable: a10313
                                              └──Desc: Variable: v
                                     └──Expression:
                                        └──Type expr: Variable: a10313
                                        └──Desc: Variable
                                           └──Variable: v
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: a10313
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Lam
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a10362
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a10362
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a10358
                                              └──Constructor type:
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: a10313
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a10362
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: a10362
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: a10358
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a10362
                                                    └──Desc: Any
                                                 └──Pattern:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a10362
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a10358
                                                    └──Desc: Variable: f
                                     └──Expression:
                                        └──Type expr: Variable: a10313
                                        └──Desc: Function
                                           └──Pattern:
                                              └──Type expr: Variable: a10362
                                              └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Variable: a10358
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a10358
                                                       └──Type expr: Variable: a10358
                                                    └──Desc: Variable
                                                       └──Variable: heval
                                                       └──Type expr: Variable: a10358
                                                 └──Expression:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: a10358
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: a10362
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: a10358
                                                          └──Desc: Variable
                                                             └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: a10362
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Con
                                                                └──Constructor argument type:
                                                                   └──Type expr: Variable: a10362
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: hterm
                                                                      └──Type expr: Variable: a10362
                                                             └──Expression:
                                                                └──Type expr: Variable: a10362
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: a10313
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: App
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: a10410
                                                          └──Type expr: Variable: a10313
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: a10410
                                              └──Constructor type:
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: a10313
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: a10410
                                                       └──Type expr: Variable: a10313
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: a10410
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: a10410
                                                          └──Type expr: Variable: a10313
                                                    └──Desc: Variable: f
                                                 └──Pattern:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: a10410
                                                    └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: a10313
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: a10410
                                                 └──Type expr: Variable: a10313
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a10410
                                                             └──Type expr: Variable: a10313
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: a10410
                                                          └──Type expr: Variable: a10313
                                                    └──Desc: Variable
                                                       └──Variable: heval
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: a10410
                                                          └──Type expr: Variable: a10313
                                                 └──Expression:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: a10410
                                                          └──Type expr: Variable: a10313
                                                    └──Desc: Variable
                                                       └──Variable: f
                                           └──Expression:
                                              └──Type expr: Variable: a10410
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a10410
                                                       └──Type expr: Variable: a10410
                                                    └──Desc: Variable
                                                       └──Variable: heval
                                                       └──Type expr: Variable: a10410
                                                 └──Expression:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: a10410
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
                   └──Variables: a10447,a10446
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: index
                            └──Type expr: Variable: a10468
                            └──Type expr: Variable: a10469
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: index
                               └──Type expr: Variable: a10468
                               └──Type expr: Variable: a10469
                            └──Desc: Variable: ix
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: index
                                     └──Type expr: Variable: a10468
                                     └──Type expr: Variable: a10469
                                  └──Desc: Variable
                                     └──Variable: ix
                               └──Type expr: Constructor: index
                                  └──Type expr: Variable: a10468
                                  └──Type expr: Variable: a10469
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: index
                                           └──Type expr: Variable: a10468
                                           └──Type expr: Variable: a10469
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Zero
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: a10468
                                                    └──Type expr: Variable: a10469
                                           └──Pattern:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 0
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: index
                                           └──Type expr: Variable: a10468
                                           └──Type expr: Variable: a10469
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: a10498
                                                    └──Type expr: Variable: a10469
                                              └──Constructor type:
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: a10468
                                                    └──Type expr: Variable: a10469
                                           └──Pattern:
                                              └──Type expr: Constructor: index
                                                 └──Type expr: Variable: a10498
                                                 └──Type expr: Variable: a10469
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
                                                                └──Type expr: Variable: a10498
                                                                └──Type expr: Variable: a10469
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: index_to_int
                                                             └──Type expr: Variable: a10469
                                                             └──Type expr: Variable: a10498
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: a10498
                                                             └──Type expr: Variable: a10469
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
                   └──Variables: a10547,a10546
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: index
                            └──Type expr: Variable: a10572
                            └──Type expr: Variable: a10573
                         └──Type expr: Arrow
                            └──Type expr: Constructor: stack
                               └──Type expr: Variable: a10572
                            └──Type expr: Variable: a10573
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: index
                               └──Type expr: Variable: a10572
                               └──Type expr: Variable: a10573
                            └──Desc: Variable: ix
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: stack
                                  └──Type expr: Variable: a10572
                               └──Type expr: Variable: a10573
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: stack
                                     └──Type expr: Variable: a10572
                                  └──Desc: Variable: s
                               └──Expression:
                                  └──Type expr: Variable: a10573
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: index
                                              └──Type expr: Variable: a10572
                                              └──Type expr: Variable: a10573
                                           └──Type expr: Constructor: stack
                                              └──Type expr: Variable: a10572
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: index
                                                 └──Type expr: Variable: a10572
                                                 └──Type expr: Variable: a10573
                                              └──Desc: Variable
                                                 └──Variable: ix
                                           └──Expression:
                                              └──Type expr: Constructor: stack
                                                 └──Type expr: Variable: a10572
                                              └──Desc: Variable
                                                 └──Variable: s
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: index
                                           └──Type expr: Variable: a10572
                                           └──Type expr: Variable: a10573
                                        └──Type expr: Constructor: stack
                                           └──Type expr: Variable: a10572
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: a10572
                                                    └──Type expr: Variable: a10573
                                                 └──Type expr: Constructor: stack
                                                    └──Type expr: Variable: a10572
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a10572
                                                       └──Type expr: Variable: a10573
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a10572
                                                                └──Type expr: Variable: a10573
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                                 └──Pattern:
                                                    └──Type expr: Constructor: stack
                                                       └──Type expr: Variable: a10572
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Push
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: a10610
                                                                └──Type expr: Variable: a10608
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: a10572
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: a10610
                                                             └──Type expr: Variable: a10608
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: a10610
                                                                └──Desc: Any
                                                             └──Pattern:
                                                                └──Type expr: Variable: a10608
                                                                └──Desc: Variable: v
                                           └──Expression:
                                              └──Type expr: Variable: a10573
                                              └──Desc: Variable
                                                 └──Variable: v
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: a10572
                                                    └──Type expr: Variable: a10573
                                                 └──Type expr: Constructor: stack
                                                    └──Type expr: Variable: a10572
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a10572
                                                       └──Type expr: Variable: a10573
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a10648
                                                                └──Type expr: Variable: a10573
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a10572
                                                                └──Type expr: Variable: a10573
                                                       └──Pattern:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: a10648
                                                             └──Type expr: Variable: a10573
                                                          └──Desc: Variable: ix
                                                 └──Pattern:
                                                    └──Type expr: Constructor: stack
                                                       └──Type expr: Variable: a10572
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Push
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: a10645
                                                                └──Type expr: Variable: a10643
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: a10572
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: a10645
                                                             └──Type expr: Variable: a10643
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: a10645
                                                                └──Desc: Variable: s
                                                             └──Pattern:
                                                                └──Type expr: Variable: a10643
                                                                └──Desc: Any
                                           └──Expression:
                                              └──Type expr: Variable: a10573
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: stack
                                                          └──Type expr: Variable: a10645
                                                       └──Type expr: Variable: a10573
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a10645
                                                                └──Type expr: Variable: a10573
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: a10645
                                                                └──Type expr: Variable: a10573
                                                          └──Desc: Variable
                                                             └──Variable: prj
                                                             └──Type expr: Variable: a10573
                                                             └──Type expr: Variable: a10645
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: a10645
                                                             └──Type expr: Variable: a10573
                                                          └──Desc: Variable
                                                             └──Variable: ix
                                                 └──Expression:
                                                    └──Type expr: Constructor: stack
                                                       └──Type expr: Variable: a10645
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
                   └──Variables: a10693,a10692
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: dterm
                            └──Type expr: Variable: a10718
                            └──Type expr: Variable: a10719
                         └──Type expr: Arrow
                            └──Type expr: Constructor: stack
                               └──Type expr: Variable: a10718
                            └──Type expr: Variable: a10719
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: dterm
                               └──Type expr: Variable: a10718
                               └──Type expr: Variable: a10719
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: stack
                                  └──Type expr: Variable: a10718
                               └──Type expr: Variable: a10719
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: stack
                                     └──Type expr: Variable: a10718
                                  └──Desc: Variable: s
                               └──Expression:
                                  └──Type expr: Variable: a10719
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: dterm
                                           └──Type expr: Variable: a10718
                                           └──Type expr: Variable: a10719
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Constructor: dterm
                                        └──Type expr: Variable: a10718
                                        └──Type expr: Variable: a10719
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a10718
                                                 └──Type expr: Variable: a10719
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: index
                                                          └──Type expr: Variable: a10718
                                                          └──Type expr: Variable: a10719
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a10718
                                                          └──Type expr: Variable: a10719
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a10718
                                                       └──Type expr: Variable: a10719
                                                    └──Desc: Variable: ix
                                           └──Expression:
                                              └──Type expr: Variable: a10719
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: stack
                                                          └──Type expr: Variable: a10718
                                                       └──Type expr: Variable: a10719
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a10718
                                                                └──Type expr: Variable: a10719
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: a10718
                                                                └──Type expr: Variable: a10719
                                                          └──Desc: Variable
                                                             └──Variable: prj
                                                             └──Type expr: Variable: a10719
                                                             └──Type expr: Variable: a10718
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: a10718
                                                             └──Type expr: Variable: a10719
                                                          └──Desc: Variable
                                                             └──Variable: ix
                                                 └──Expression:
                                                    └──Type expr: Constructor: stack
                                                       └──Type expr: Variable: a10718
                                                    └──Desc: Variable
                                                       └──Variable: s
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a10718
                                                 └──Type expr: Variable: a10719
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_con
                                                    └──Constructor argument type:
                                                       └──Type expr: Variable: a10719
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a10718
                                                          └──Type expr: Variable: a10719
                                                 └──Pattern:
                                                    └──Type expr: Variable: a10719
                                                    └──Desc: Variable: v
                                           └──Expression:
                                              └──Type expr: Variable: a10719
                                              └──Desc: Variable
                                                 └──Variable: v
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a10718
                                                 └──Type expr: Variable: a10719
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_lam
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a10718
                                                             └──Type expr: Variable: a10776
                                                          └──Type expr: Variable: a10774
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a10718
                                                          └──Type expr: Variable: a10719
                                                 └──Pattern:
                                                    └──Type expr: Constructor: dterm
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a10718
                                                          └──Type expr: Variable: a10776
                                                       └──Type expr: Variable: a10774
                                                    └──Desc: Variable: b
                                           └──Expression:
                                              └──Type expr: Variable: a10719
                                              └──Desc: Function
                                                 └──Pattern:
                                                    └──Type expr: Variable: a10776
                                                    └──Desc: Variable: x
                                                 └──Expression:
                                                    └──Type expr: Variable: a10774
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a10718
                                                                   └──Type expr: Variable: a10776
                                                             └──Type expr: Variable: a10774
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a10718
                                                                         └──Type expr: Variable: a10776
                                                                      └──Type expr: Variable: a10774
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a10718
                                                                            └──Type expr: Variable: a10776
                                                                      └──Type expr: Variable: a10774
                                                                └──Desc: Variable
                                                                   └──Variable: deval
                                                                   └──Type expr: Variable: a10774
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a10718
                                                                      └──Type expr: Variable: a10776
                                                             └──Expression:
                                                                └──Type expr: Constructor: dterm
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a10718
                                                                      └──Type expr: Variable: a10776
                                                                   └──Type expr: Variable: a10774
                                                                └──Desc: Variable
                                                                   └──Variable: b
                                                       └──Expression:
                                                          └──Type expr: Constructor: stack
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a10718
                                                                └──Type expr: Variable: a10776
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Push
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Variable: a10718
                                                                      └──Type expr: Variable: a10776
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: stack
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a10718
                                                                         └──Type expr: Variable: a10776
                                                             └──Expression:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: stack
                                                                      └──Type expr: Variable: a10718
                                                                   └──Type expr: Variable: a10776
                                                                └──Desc: Tuple
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Variable: a10718
                                                                      └──Desc: Variable
                                                                         └──Variable: s
                                                                   └──Expression:
                                                                      └──Type expr: Variable: a10776
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a10718
                                                 └──Type expr: Variable: a10719
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_app
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a10718
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a10839
                                                                └──Type expr: Variable: a10719
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a10718
                                                             └──Type expr: Variable: a10839
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a10718
                                                          └──Type expr: Variable: a10719
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a10718
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a10839
                                                             └──Type expr: Variable: a10719
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a10718
                                                          └──Type expr: Variable: a10839
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a10718
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a10839
                                                                └──Type expr: Variable: a10719
                                                          └──Desc: Variable: f
                                                       └──Pattern:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a10718
                                                             └──Type expr: Variable: a10839
                                                          └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Variable: a10719
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: a10839
                                                       └──Type expr: Variable: a10719
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: a10718
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a10839
                                                                └──Type expr: Variable: a10719
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Variable: a10718
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: a10839
                                                                         └──Type expr: Variable: a10719
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Variable: a10718
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: a10839
                                                                         └──Type expr: Variable: a10719
                                                                └──Desc: Variable
                                                                   └──Variable: deval
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a10839
                                                                      └──Type expr: Variable: a10719
                                                                   └──Type expr: Variable: a10718
                                                             └──Expression:
                                                                └──Type expr: Constructor: dterm
                                                                   └──Type expr: Variable: a10718
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a10839
                                                                      └──Type expr: Variable: a10719
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Constructor: stack
                                                             └──Type expr: Variable: a10718
                                                          └──Desc: Variable
                                                             └──Variable: s
                                                 └──Expression:
                                                    └──Type expr: Variable: a10839
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: a10718
                                                             └──Type expr: Variable: a10839
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Variable: a10718
                                                                      └──Type expr: Variable: a10839
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Variable: a10718
                                                                      └──Type expr: Variable: a10839
                                                                └──Desc: Variable
                                                                   └──Variable: deval
                                                                   └──Type expr: Variable: a10839
                                                                   └──Type expr: Variable: a10718
                                                             └──Expression:
                                                                └──Type expr: Constructor: dterm
                                                                   └──Type expr: Variable: a10718
                                                                   └──Type expr: Variable: a10839
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: stack
                                                             └──Type expr: Variable: a10718
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
                   └──Variables: a10893,a10892
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: layout
                            └──Type expr: Variable: a10914
                            └──Type expr: Variable: a10915
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: layout
                               └──Type expr: Variable: a10914
                               └──Type expr: Variable: a10915
                            └──Desc: Variable: l
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: layout
                                     └──Type expr: Variable: a10914
                                     └──Type expr: Variable: a10915
                                  └──Desc: Variable
                                     └──Variable: l
                               └──Type expr: Constructor: layout
                                  └──Type expr: Variable: a10914
                                  └──Type expr: Variable: a10915
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: a10914
                                           └──Type expr: Variable: a10915
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Empty_layout
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: a10914
                                                    └──Type expr: Variable: a10915
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 0
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: a10914
                                           └──Type expr: Variable: a10915
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Push_layout
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a10950
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: a10914
                                                       └──Type expr: Variable: a10948
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a10914
                                                       └──Type expr: Variable: a10950
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: a10914
                                                    └──Type expr: Variable: a10915
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a10950
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: a10914
                                                    └──Type expr: Variable: a10948
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: a10914
                                                    └──Type expr: Variable: a10950
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a10950
                                                    └──Desc: Any
                                                 └──Pattern:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: a10914
                                                       └──Type expr: Variable: a10948
                                                    └──Desc: Variable: l
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a10914
                                                       └──Type expr: Variable: a10950
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
                                                                └──Type expr: Variable: a10914
                                                                └──Type expr: Variable: a10948
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: size
                                                             └──Type expr: Variable: a10948
                                                             └──Type expr: Variable: a10914
                                                       └──Expression:
                                                          └──Type expr: Constructor: layout
                                                             └──Type expr: Variable: a10914
                                                             └──Type expr: Variable: a10948
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
                   └──Variables: a10999,a11002,a11001
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: layout
                            └──Type expr: Variable: a11029
                            └──Type expr: Variable: a11030
                         └──Type expr: Constructor: layout
                            └──Type expr: Tuple
                               └──Type expr: Variable: a11029
                               └──Type expr: Variable: a11061
                            └──Type expr: Variable: a11030
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: layout
                               └──Type expr: Variable: a11029
                               └──Type expr: Variable: a11030
                            └──Desc: Variable: l
                         └──Expression:
                            └──Type expr: Constructor: layout
                               └──Type expr: Tuple
                                  └──Type expr: Variable: a11029
                                  └──Type expr: Variable: a11061
                               └──Type expr: Variable: a11030
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: layout
                                     └──Type expr: Variable: a11029
                                     └──Type expr: Variable: a11030
                                  └──Desc: Variable
                                     └──Variable: l
                               └──Type expr: Constructor: layout
                                  └──Type expr: Variable: a11029
                                  └──Type expr: Variable: a11030
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: a11029
                                           └──Type expr: Variable: a11030
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Empty_layout
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: a11029
                                                    └──Type expr: Variable: a11030
                                     └──Expression:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a11029
                                              └──Type expr: Variable: a11061
                                           └──Type expr: Variable: a11030
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Empty_layout
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a11029
                                                       └──Type expr: Variable: a11061
                                                    └──Type expr: Variable: a11030
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: a11029
                                           └──Type expr: Variable: a11030
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Push_layout
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a11091
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: a11029
                                                       └──Type expr: Variable: a11089
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a11029
                                                       └──Type expr: Variable: a11091
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: a11029
                                                    └──Type expr: Variable: a11030
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a11091
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: a11029
                                                    └──Type expr: Variable: a11089
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: a11029
                                                    └──Type expr: Variable: a11091
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a11091
                                                    └──Desc: Variable: t
                                                 └──Pattern:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: a11029
                                                       └──Type expr: Variable: a11089
                                                    └──Desc: Variable: l
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a11029
                                                       └──Type expr: Variable: a11091
                                                    └──Desc: Variable: ix
                                     └──Expression:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a11029
                                              └──Type expr: Variable: a11061
                                           └──Type expr: Variable: a11030
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Push_layout
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a11091
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a11029
                                                          └──Type expr: Variable: a11061
                                                       └──Type expr: Variable: a11089
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a11029
                                                          └──Type expr: Variable: a11061
                                                       └──Type expr: Variable: a11091
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a11029
                                                       └──Type expr: Variable: a11061
                                                    └──Type expr: Variable: a11030
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a11091
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a11029
                                                       └──Type expr: Variable: a11061
                                                    └──Type expr: Variable: a11089
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a11029
                                                       └──Type expr: Variable: a11061
                                                    └──Type expr: Variable: a11091
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a11091
                                                    └──Desc: Variable
                                                       └──Variable: t
                                                 └──Expression:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a11029
                                                          └──Type expr: Variable: a11061
                                                       └──Type expr: Variable: a11089
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: a11029
                                                                └──Type expr: Variable: a11089
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a11029
                                                                   └──Type expr: Variable: a11061
                                                                └──Type expr: Variable: a11089
                                                          └──Desc: Variable
                                                             └──Variable: inc
                                                             └──Type expr: Variable: a11061
                                                             └──Type expr: Variable: a11089
                                                             └──Type expr: Variable: a11029
                                                       └──Expression:
                                                          └──Type expr: Constructor: layout
                                                             └──Type expr: Variable: a11029
                                                             └──Type expr: Variable: a11089
                                                          └──Desc: Variable
                                                             └──Variable: l
                                                 └──Expression:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a11029
                                                          └──Type expr: Variable: a11061
                                                       └──Type expr: Variable: a11091
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a11029
                                                                └──Type expr: Variable: a11091
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a11029
                                                                   └──Type expr: Variable: a11061
                                                                └──Type expr: Variable: a11091
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: a11029
                                                             └──Type expr: Variable: a11091
                                                          └──Desc: Variable
                                                             └──Variable: ix
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: prjl
                └──Abstraction:
                   └──Variables: a11180,a11179,a11183
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: a11215
                         └──Type expr: Arrow
                            └──Type expr: Constructor: int
                            └──Type expr: Arrow
                               └──Type expr: Constructor: layout
                                  └──Type expr: Variable: a11234
                                  └──Type expr: Variable: a11235
                               └──Type expr: Constructor: index
                                  └──Type expr: Variable: a11234
                                  └──Type expr: Variable: a11215
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: a11215
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: layout
                                     └──Type expr: Variable: a11234
                                     └──Type expr: Variable: a11235
                                  └──Type expr: Constructor: index
                                     └──Type expr: Variable: a11234
                                     └──Type expr: Variable: a11215
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable: n
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: layout
                                        └──Type expr: Variable: a11234
                                        └──Type expr: Variable: a11235
                                     └──Type expr: Constructor: index
                                        └──Type expr: Variable: a11234
                                        └──Type expr: Variable: a11215
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: a11234
                                           └──Type expr: Variable: a11235
                                        └──Desc: Variable: l
                                     └──Expression:
                                        └──Type expr: Constructor: index
                                           └──Type expr: Variable: a11234
                                           └──Type expr: Variable: a11215
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: layout
                                                 └──Type expr: Variable: a11234
                                                 └──Type expr: Variable: a11235
                                              └──Desc: Variable
                                                 └──Variable: l
                                           └──Type expr: Constructor: layout
                                              └──Type expr: Variable: a11234
                                              └──Type expr: Variable: a11235
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: a11234
                                                       └──Type expr: Variable: a11235
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Empty_layout
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: a11234
                                                                └──Type expr: Variable: a11235
                                                 └──Expression:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a11234
                                                       └──Type expr: Variable: a11215
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: string
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a11234
                                                                └──Type expr: Variable: a11215
                                                          └──Desc: Variable
                                                             └──Variable: fail_with
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a11234
                                                                └──Type expr: Variable: a11215
                                                       └──Expression:
                                                          └──Type expr: Constructor: string
                                                          └──Desc: Constant: convert prjl
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: a11234
                                                       └──Type expr: Variable: a11235
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Push_layout
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a11284
                                                                └──Type expr: Constructor: layout
                                                                   └──Type expr: Variable: a11234
                                                                   └──Type expr: Variable: a11282
                                                                └──Type expr: Constructor: index
                                                                   └──Type expr: Variable: a11234
                                                                   └──Type expr: Variable: a11284
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: a11234
                                                                └──Type expr: Variable: a11235
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a11284
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: a11234
                                                                └──Type expr: Variable: a11282
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a11234
                                                                └──Type expr: Variable: a11284
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a11284
                                                                └──Desc: Variable: t'
                                                             └──Pattern:
                                                                └──Type expr: Constructor: layout
                                                                   └──Type expr: Variable: a11234
                                                                   └──Type expr: Variable: a11282
                                                                └──Desc: Variable: l
                                                             └──Pattern:
                                                                └──Type expr: Constructor: index
                                                                   └──Type expr: Variable: a11234
                                                                   └──Type expr: Variable: a11284
                                                                └──Desc: Variable: ix
                                                 └──Expression:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a11234
                                                       └──Type expr: Variable: a11215
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
                                                             └──Type expr: Variable: a11234
                                                             └──Type expr: Variable: a11215
                                                          └──Desc: Match
                                                             └──Expression:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: a11215
                                                                   └──Type expr: Variable: a11284
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a11284
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: a11215
                                                                            └──Type expr: Variable: a11284
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: ty
                                                                                  └──Type expr: Variable: a11215
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: ty
                                                                                     └──Type expr: Variable: a11284
                                                                                  └──Type expr: Constructor: eq
                                                                                     └──Type expr: Variable: a11215
                                                                                     └──Type expr: Variable: a11284
                                                                            └──Desc: Variable
                                                                               └──Variable: check_eq
                                                                               └──Type expr: Variable: a11284
                                                                               └──Type expr: Variable: a11215
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: a11215
                                                                            └──Desc: Variable
                                                                               └──Variable: t
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a11284
                                                                      └──Desc: Variable
                                                                         └──Variable: t'
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a11215
                                                                └──Type expr: Variable: a11284
                                                             └──Cases:
                                                                └──Case:
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: eq
                                                                         └──Type expr: Variable: a11215
                                                                         └──Type expr: Variable: a11284
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Refl
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: eq
                                                                                  └──Type expr: Variable: a11215
                                                                                  └──Type expr: Variable: a11284
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: index
                                                                         └──Type expr: Variable: a11234
                                                                         └──Type expr: Variable: a11215
                                                                      └──Desc: Variable
                                                                         └──Variable: ix
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: a11234
                                                             └──Type expr: Variable: a11215
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: layout
                                                                      └──Type expr: Variable: a11234
                                                                      └──Type expr: Variable: a11282
                                                                   └──Type expr: Constructor: index
                                                                      └──Type expr: Variable: a11234
                                                                      └──Type expr: Variable: a11215
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: int
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: layout
                                                                               └──Type expr: Variable: a11234
                                                                               └──Type expr: Variable: a11282
                                                                            └──Type expr: Constructor: index
                                                                               └──Type expr: Variable: a11234
                                                                               └──Type expr: Variable: a11215
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: ty
                                                                                  └──Type expr: Variable: a11215
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: int
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: layout
                                                                                        └──Type expr: Variable: a11234
                                                                                        └──Type expr: Variable: a11282
                                                                                     └──Type expr: Constructor: index
                                                                                        └──Type expr: Variable: a11234
                                                                                        └──Type expr: Variable: a11215
                                                                            └──Desc: Variable
                                                                               └──Variable: prjl
                                                                               └──Type expr: Variable: a11282
                                                                               └──Type expr: Variable: a11234
                                                                               └──Type expr: Variable: a11215
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: a11215
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
                                                                   └──Type expr: Variable: a11234
                                                                   └──Type expr: Variable: a11282
                                                                └──Desc: Variable
                                                                   └──Variable: l
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: convert
                └──Abstraction:
                   └──Variables: a11409,a11412
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: layout
                            └──Type expr: Variable: a11441
                            └──Type expr: Variable: a11441
                         └──Type expr: Arrow
                            └──Type expr: Constructor: hterm
                               └──Type expr: Variable: a11451
                            └──Type expr: Constructor: dterm
                               └──Type expr: Variable: a11441
                               └──Type expr: Variable: a11451
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: layout
                               └──Type expr: Variable: a11441
                               └──Type expr: Variable: a11441
                            └──Desc: Variable: l
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: hterm
                                  └──Type expr: Variable: a11451
                               └──Type expr: Constructor: dterm
                                  └──Type expr: Variable: a11441
                                  └──Type expr: Variable: a11451
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: hterm
                                     └──Type expr: Variable: a11451
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Constructor: dterm
                                     └──Type expr: Variable: a11441
                                     └──Type expr: Variable: a11451
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: a11451
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Constructor: hterm
                                        └──Type expr: Variable: a11451
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: hterm
                                                 └──Type expr: Variable: a11451
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Tag
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a11451
                                                          └──Type expr: Constructor: int
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a11451
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: a11451
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a11451
                                                          └──Desc: Variable: t
                                                       └──Pattern:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable: sz
                                           └──Expression:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a11441
                                                 └──Type expr: Variable: a11451
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: index
                                                          └──Type expr: Variable: a11441
                                                          └──Type expr: Variable: a11451
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a11441
                                                          └──Type expr: Variable: a11451
                                                 └──Expression:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a11441
                                                       └──Type expr: Variable: a11451
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: a11441
                                                                └──Type expr: Variable: a11441
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a11441
                                                                └──Type expr: Variable: a11451
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: int
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Variable: a11441
                                                                         └──Type expr: Variable: a11441
                                                                      └──Type expr: Constructor: index
                                                                         └──Type expr: Variable: a11441
                                                                         └──Type expr: Variable: a11451
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a11451
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: int
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: layout
                                                                                  └──Type expr: Variable: a11441
                                                                                  └──Type expr: Variable: a11441
                                                                               └──Type expr: Constructor: index
                                                                                  └──Type expr: Variable: a11441
                                                                                  └──Type expr: Variable: a11451
                                                                      └──Desc: Variable
                                                                         └──Variable: prjl
                                                                         └──Type expr: Variable: a11441
                                                                         └──Type expr: Variable: a11441
                                                                         └──Type expr: Variable: a11451
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a11451
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
                                                                                                    └──Type expr: Variable: a11441
                                                                                                    └──Type expr: Variable: a11441
                                                                                                 └──Type expr: Constructor: int
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: size
                                                                                                 └──Type expr: Variable: a11441
                                                                                                 └──Type expr: Variable: a11441
                                                                                           └──Expression:
                                                                                              └──Type expr: Constructor: layout
                                                                                                 └──Type expr: Variable: a11441
                                                                                                 └──Type expr: Variable: a11441
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
                                                             └──Type expr: Variable: a11441
                                                             └──Type expr: Variable: a11441
                                                          └──Desc: Variable
                                                             └──Variable: l
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: hterm
                                                 └──Type expr: Variable: a11451
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Con
                                                    └──Constructor argument type:
                                                       └──Type expr: Variable: a11451
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a11451
                                                 └──Pattern:
                                                    └──Type expr: Variable: a11451
                                                    └──Desc: Variable: v
                                           └──Expression:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a11441
                                                 └──Type expr: Variable: a11451
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_con
                                                    └──Constructor argument type:
                                                       └──Type expr: Variable: a11451
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a11441
                                                          └──Type expr: Variable: a11451
                                                 └──Expression:
                                                    └──Type expr: Variable: a11451
                                                    └──Desc: Variable
                                                       └──Variable: v
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: hterm
                                                 └──Type expr: Variable: a11451
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Lam
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a11590
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: a11590
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: a11586
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a11451
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: a11590
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: a11590
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: a11586
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a11590
                                                          └──Desc: Variable: t
                                                       └──Pattern:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: a11590
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: a11586
                                                          └──Desc: Variable: f
                                           └──Expression:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a11441
                                                 └──Type expr: Variable: a11451
                                              └──Desc: Let
                                                 └──Value bindings:
                                                    └──Value binding:
                                                       └──Pattern:
                                                          └──Type expr: Constructor: layout
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a11441
                                                                └──Type expr: Variable: a11590
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a11441
                                                                └──Type expr: Variable: a11590
                                                          └──Desc: Variable: l'
                                                       └──Abstraction:
                                                          └──Variables:
                                                          └──Expression:
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a11441
                                                                   └──Type expr: Variable: a11590
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a11441
                                                                   └──Type expr: Variable: a11590
                                                             └──Desc: Construct
                                                                └──Constructor description:
                                                                   └──Name: Push_layout
                                                                   └──Constructor argument type:
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a11590
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a11441
                                                                               └──Type expr: Variable: a11590
                                                                            └──Type expr: Variable: a11441
                                                                         └──Type expr: Constructor: index
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a11441
                                                                               └──Type expr: Variable: a11590
                                                                            └──Type expr: Variable: a11590
                                                                   └──Constructor type:
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a11441
                                                                            └──Type expr: Variable: a11590
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a11441
                                                                            └──Type expr: Variable: a11590
                                                                └──Expression:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a11590
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a11441
                                                                            └──Type expr: Variable: a11590
                                                                         └──Type expr: Variable: a11441
                                                                      └──Type expr: Constructor: index
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a11441
                                                                            └──Type expr: Variable: a11590
                                                                         └──Type expr: Variable: a11590
                                                                   └──Desc: Tuple
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a11590
                                                                         └──Desc: Variable
                                                                            └──Variable: t
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a11441
                                                                               └──Type expr: Variable: a11590
                                                                            └──Type expr: Variable: a11441
                                                                         └──Desc: Application
                                                                            └──Expression:
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: layout
                                                                                     └──Type expr: Variable: a11441
                                                                                     └──Type expr: Variable: a11441
                                                                                  └──Type expr: Constructor: layout
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Variable: a11441
                                                                                        └──Type expr: Variable: a11590
                                                                                     └──Type expr: Variable: a11441
                                                                               └──Desc: Variable
                                                                                  └──Variable: inc
                                                                                  └──Type expr: Variable: a11590
                                                                                  └──Type expr: Variable: a11441
                                                                                  └──Type expr: Variable: a11441
                                                                            └──Expression:
                                                                               └──Type expr: Constructor: layout
                                                                                  └──Type expr: Variable: a11441
                                                                                  └──Type expr: Variable: a11441
                                                                               └──Desc: Variable
                                                                                  └──Variable: l
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: index
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a11441
                                                                               └──Type expr: Variable: a11590
                                                                            └──Type expr: Variable: a11590
                                                                         └──Desc: Construct
                                                                            └──Constructor description:
                                                                               └──Name: Zero
                                                                               └──Constructor argument type:
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Constructor type:
                                                                                  └──Type expr: Constructor: index
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Variable: a11441
                                                                                        └──Type expr: Variable: a11590
                                                                                     └──Type expr: Variable: a11590
                                                                            └──Expression:
                                                                               └──Type expr: Constructor: unit
                                                                               └──Desc: Constant: ()
                                                 └──Expression:
                                                    └──Type expr: Constructor: dterm
                                                       └──Type expr: Variable: a11441
                                                       └──Type expr: Variable: a11451
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: D_lam
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: dterm
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a11441
                                                                   └──Type expr: Variable: a11590
                                                                └──Type expr: Variable: a11586
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: dterm
                                                                └──Type expr: Variable: a11441
                                                                └──Type expr: Variable: a11451
                                                       └──Expression:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a11441
                                                                └──Type expr: Variable: a11590
                                                             └──Type expr: Variable: a11586
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: hterm
                                                                      └──Type expr: Variable: a11586
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a11441
                                                                         └──Type expr: Variable: a11590
                                                                      └──Type expr: Variable: a11586
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a11441
                                                                               └──Type expr: Variable: a11590
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a11441
                                                                               └──Type expr: Variable: a11590
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: hterm
                                                                               └──Type expr: Variable: a11586
                                                                            └──Type expr: Constructor: dterm
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: a11441
                                                                                  └──Type expr: Variable: a11590
                                                                               └──Type expr: Variable: a11586
                                                                      └──Desc: Variable
                                                                         └──Variable: convert
                                                                         └──Type expr: Variable: a11586
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a11441
                                                                            └──Type expr: Variable: a11590
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a11441
                                                                            └──Type expr: Variable: a11590
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a11441
                                                                            └──Type expr: Variable: a11590
                                                                      └──Desc: Variable
                                                                         └──Variable: l'
                                                             └──Expression:
                                                                └──Type expr: Constructor: hterm
                                                                   └──Type expr: Variable: a11586
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: hterm
                                                                            └──Type expr: Variable: a11590
                                                                         └──Type expr: Constructor: hterm
                                                                            └──Type expr: Variable: a11586
                                                                      └──Desc: Variable
                                                                         └──Variable: f
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: hterm
                                                                         └──Type expr: Variable: a11590
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Tag
                                                                            └──Constructor argument type:
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Constructor: ty
                                                                                     └──Type expr: Variable: a11590
                                                                                  └──Type expr: Constructor: int
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: hterm
                                                                                  └──Type expr: Variable: a11590
                                                                         └──Expression:
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Constructor: ty
                                                                                  └──Type expr: Variable: a11590
                                                                               └──Type expr: Constructor: int
                                                                            └──Desc: Tuple
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: ty
                                                                                     └──Type expr: Variable: a11590
                                                                                  └──Desc: Variable
                                                                                     └──Variable: t
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: int
                                                                                  └──Desc: Application
                                                                                     └──Expression:
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Constructor: layout
                                                                                              └──Type expr: Variable: a11441
                                                                                              └──Type expr: Variable: a11441
                                                                                           └──Type expr: Constructor: int
                                                                                        └──Desc: Variable
                                                                                           └──Variable: size
                                                                                           └──Type expr: Variable: a11441
                                                                                           └──Type expr: Variable: a11441
                                                                                     └──Expression:
                                                                                        └──Type expr: Constructor: layout
                                                                                           └──Type expr: Variable: a11441
                                                                                           └──Type expr: Variable: a11441
                                                                                        └──Desc: Variable
                                                                                           └──Variable: l
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: hterm
                                                 └──Type expr: Variable: a11451
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: App
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a11728
                                                                └──Type expr: Variable: a11451
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: a11728
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a11451
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a11728
                                                             └──Type expr: Variable: a11451
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a11728
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a11728
                                                                └──Type expr: Variable: a11451
                                                          └──Desc: Variable: f
                                                       └──Pattern:
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: a11728
                                                          └──Desc: Variable: a
                                           └──Expression:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a11441
                                                 └──Type expr: Variable: a11451
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_app
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a11441
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a11728
                                                                └──Type expr: Variable: a11451
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a11441
                                                             └──Type expr: Variable: a11728
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a11441
                                                          └──Type expr: Variable: a11451
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a11441
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a11728
                                                             └──Type expr: Variable: a11451
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a11441
                                                          └──Type expr: Variable: a11728
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a11441
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a11728
                                                                └──Type expr: Variable: a11451
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: hterm
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: a11728
                                                                         └──Type expr: Variable: a11451
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Variable: a11441
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: a11728
                                                                         └──Type expr: Variable: a11451
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Variable: a11441
                                                                            └──Type expr: Variable: a11441
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: hterm
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: a11728
                                                                                  └──Type expr: Variable: a11451
                                                                            └──Type expr: Constructor: dterm
                                                                               └──Type expr: Variable: a11441
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: a11728
                                                                                  └──Type expr: Variable: a11451
                                                                      └──Desc: Variable
                                                                         └──Variable: convert
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Variable: a11728
                                                                            └──Type expr: Variable: a11451
                                                                         └──Type expr: Variable: a11441
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Variable: a11441
                                                                         └──Type expr: Variable: a11441
                                                                      └──Desc: Variable
                                                                         └──Variable: l
                                                             └──Expression:
                                                                └──Type expr: Constructor: hterm
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a11728
                                                                      └──Type expr: Variable: a11451
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a11441
                                                             └──Type expr: Variable: a11728
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: hterm
                                                                      └──Type expr: Variable: a11728
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Variable: a11441
                                                                      └──Type expr: Variable: a11728
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Variable: a11441
                                                                            └──Type expr: Variable: a11441
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: hterm
                                                                               └──Type expr: Variable: a11728
                                                                            └──Type expr: Constructor: dterm
                                                                               └──Type expr: Variable: a11441
                                                                               └──Type expr: Variable: a11728
                                                                      └──Desc: Variable
                                                                         └──Variable: convert
                                                                         └──Type expr: Variable: a11728
                                                                         └──Type expr: Variable: a11441
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Variable: a11441
                                                                         └──Type expr: Variable: a11441
                                                                      └──Desc: Variable
                                                                         └──Variable: l
                                                             └──Expression:
                                                                └──Type expr: Constructor: hterm
                                                                   └──Type expr: Variable: a11728
                                                                └──Desc: Variable
                                                                   └──Variable: a |}]