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
                   └──Variables: a8854,a8856
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: a8882
                         └──Type expr: Arrow
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: a8892
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: a8882
                               └──Type expr: Variable: a8892
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: a8882
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: ty
                                  └──Type expr: Variable: a8892
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: a8882
                                  └──Type expr: Variable: a8892
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: ty
                                     └──Type expr: Variable: a8892
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: a8882
                                     └──Type expr: Variable: a8892
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: ty
                                              └──Type expr: Variable: a8882
                                           └──Type expr: Constructor: ty
                                              └──Type expr: Variable: a8892
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: a8882
                                              └──Desc: Variable
                                                 └──Variable: t1
                                           └──Expression:
                                              └──Type expr: Constructor: ty
                                                 └──Type expr: Variable: a8892
                                              └──Desc: Variable
                                                 └──Variable: t2
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: ty
                                           └──Type expr: Variable: a8882
                                        └──Type expr: Constructor: ty
                                           └──Type expr: Variable: a8892
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a8882
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a8892
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a8882
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a8882
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a8892
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a8892
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a8882
                                                 └──Type expr: Variable: a8892
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Refl
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a8882
                                                          └──Type expr: Variable: a8882
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a8882
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a8892
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a8882
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: String
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a8882
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a8892
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: String
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a8892
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a8882
                                                 └──Type expr: Variable: a8892
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Refl
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a8882
                                                          └──Type expr: Variable: a8882
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a8882
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a8892
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a8882
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: List
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a8974
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a8882
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a8974
                                                          └──Desc: Variable: t1
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a8892
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: List
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a8971
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a8892
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a8971
                                                          └──Desc: Variable: t2
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a8882
                                                 └──Type expr: Variable: a8892
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a8974
                                                       └──Type expr: Variable: a8971
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a8971
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a8974
                                                                └──Type expr: Variable: a8971
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: a8974
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a8971
                                                                      └──Type expr: Constructor: eq
                                                                         └──Type expr: Variable: a8974
                                                                         └──Type expr: Variable: a8971
                                                                └──Desc: Variable
                                                                   └──Variable: check_eq
                                                                   └──Type expr: Variable: a8971
                                                                   └──Type expr: Variable: a8974
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a8974
                                                                └──Desc: Variable
                                                                   └──Variable: t1
                                                       └──Expression:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a8971
                                                          └──Desc: Variable
                                                             └──Variable: t2
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: a8974
                                                    └──Type expr: Variable: a8971
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a8974
                                                             └──Type expr: Variable: a8971
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Refl
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a8974
                                                                      └──Type expr: Variable: a8971
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a8882
                                                             └──Type expr: Variable: a8892
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Refl
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a8882
                                                                      └──Type expr: Variable: a8882
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a8882
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a8892
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a8882
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Pair
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a9056
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a9054
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a8882
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a9056
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a9054
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a9056
                                                                └──Desc: Variable: t11
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a9054
                                                                └──Desc: Variable: t12
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a8892
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Pair
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a9050
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a9048
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a8892
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a9050
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a9048
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a9050
                                                                └──Desc: Variable: t21
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a9048
                                                                └──Desc: Variable: t22
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a8882
                                                 └──Type expr: Variable: a8892
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a9056
                                                          └──Type expr: Variable: a9050
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a9054
                                                          └──Type expr: Variable: a9048
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a9056
                                                             └──Type expr: Variable: a9050
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: a9050
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a9056
                                                                      └──Type expr: Variable: a9050
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a9056
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: a9050
                                                                            └──Type expr: Constructor: eq
                                                                               └──Type expr: Variable: a9056
                                                                               └──Type expr: Variable: a9050
                                                                      └──Desc: Variable
                                                                         └──Variable: check_eq
                                                                         └──Type expr: Variable: a9050
                                                                         └──Type expr: Variable: a9056
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a9056
                                                                      └──Desc: Variable
                                                                         └──Variable: t11
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a9050
                                                                └──Desc: Variable
                                                                   └──Variable: t21
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a9054
                                                             └──Type expr: Variable: a9048
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: a9048
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a9054
                                                                      └──Type expr: Variable: a9048
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a9054
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: a9048
                                                                            └──Type expr: Constructor: eq
                                                                               └──Type expr: Variable: a9054
                                                                               └──Type expr: Variable: a9048
                                                                      └──Desc: Variable
                                                                         └──Variable: check_eq
                                                                         └──Type expr: Variable: a9048
                                                                         └──Type expr: Variable: a9054
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a9054
                                                                      └──Desc: Variable
                                                                         └──Variable: t12
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a9048
                                                                └──Desc: Variable
                                                                   └──Variable: t22
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a9056
                                                       └──Type expr: Variable: a9050
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a9054
                                                       └──Type expr: Variable: a9048
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a9056
                                                                └──Type expr: Variable: a9050
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a9054
                                                                └──Type expr: Variable: a9048
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: a9056
                                                                   └──Type expr: Variable: a9050
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: a9056
                                                                            └──Type expr: Variable: a9050
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: a9054
                                                                   └──Type expr: Variable: a9048
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: a9054
                                                                            └──Type expr: Variable: a9048
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a8882
                                                             └──Type expr: Variable: a8892
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Refl
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a8882
                                                                      └──Type expr: Variable: a8882
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a8882
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a8892
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a8882
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fun
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a9177
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a9175
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a8882
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a9177
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a9175
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a9177
                                                                └──Desc: Variable: t11
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a9175
                                                                └──Desc: Variable: t12
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a8892
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fun
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a9171
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a9169
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a8892
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a9171
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a9169
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a9171
                                                                └──Desc: Variable: t21
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a9169
                                                                └──Desc: Variable: t22
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a8882
                                                 └──Type expr: Variable: a8892
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a9177
                                                          └──Type expr: Variable: a9171
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a9175
                                                          └──Type expr: Variable: a9169
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a9177
                                                             └──Type expr: Variable: a9171
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: a9171
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a9177
                                                                      └──Type expr: Variable: a9171
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a9177
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: a9171
                                                                            └──Type expr: Constructor: eq
                                                                               └──Type expr: Variable: a9177
                                                                               └──Type expr: Variable: a9171
                                                                      └──Desc: Variable
                                                                         └──Variable: check_eq
                                                                         └──Type expr: Variable: a9171
                                                                         └──Type expr: Variable: a9177
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a9177
                                                                      └──Desc: Variable
                                                                         └──Variable: t11
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a9171
                                                                └──Desc: Variable
                                                                   └──Variable: t21
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a9175
                                                             └──Type expr: Variable: a9169
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ty
                                                                      └──Type expr: Variable: a9169
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a9175
                                                                      └──Type expr: Variable: a9169
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a9175
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: a9169
                                                                            └──Type expr: Constructor: eq
                                                                               └──Type expr: Variable: a9175
                                                                               └──Type expr: Variable: a9169
                                                                      └──Desc: Variable
                                                                         └──Variable: check_eq
                                                                         └──Type expr: Variable: a9169
                                                                         └──Type expr: Variable: a9175
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a9175
                                                                      └──Desc: Variable
                                                                         └──Variable: t12
                                                             └──Expression:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a9169
                                                                └──Desc: Variable
                                                                   └──Variable: t22
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a9177
                                                       └──Type expr: Variable: a9171
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a9175
                                                       └──Type expr: Variable: a9169
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a9177
                                                                └──Type expr: Variable: a9171
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a9175
                                                                └──Type expr: Variable: a9169
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: a9177
                                                                   └──Type expr: Variable: a9171
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: a9177
                                                                            └──Type expr: Variable: a9171
                                                             └──Pattern:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: a9175
                                                                   └──Type expr: Variable: a9169
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Refl
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: a9175
                                                                            └──Type expr: Variable: a9169
                                                       └──Expression:
                                                          └──Type expr: Constructor: eq
                                                             └──Type expr: Variable: a8882
                                                             └──Type expr: Variable: a8892
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Refl
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: eq
                                                                      └──Type expr: Variable: a8882
                                                                      └──Type expr: Variable: a8882
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: ty
                         └──Type expr: Variable: a9284
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: a9294
                         └──Type expr: Arrow
                            └──Type expr: Variable: a9284
                            └──Type expr: Variable: a9294
                   └──Desc: Variable: cast
                └──Abstraction:
                   └──Variables: a9284,a9294
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: a9284
                         └──Type expr: Arrow
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: a9294
                            └──Type expr: Arrow
                               └──Type expr: Variable: a9284
                               └──Type expr: Variable: a9294
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: a9284
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: ty
                                  └──Type expr: Variable: a9294
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a9284
                                  └──Type expr: Variable: a9294
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: ty
                                     └──Type expr: Variable: a9294
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a9284
                                     └──Type expr: Variable: a9294
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: a9284
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: a9294
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: eq
                                                 └──Type expr: Variable: a9284
                                                 └──Type expr: Variable: a9294
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: a9294
                                                       └──Type expr: Constructor: eq
                                                          └──Type expr: Variable: a9284
                                                          └──Type expr: Variable: a9294
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a9284
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a9294
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: a9284
                                                                   └──Type expr: Variable: a9294
                                                          └──Desc: Variable
                                                             └──Variable: check_eq
                                                             └──Type expr: Variable: a9294
                                                             └──Type expr: Variable: a9284
                                                       └──Expression:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a9284
                                                          └──Desc: Variable
                                                             └──Variable: t1
                                                 └──Expression:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a9294
                                                    └──Desc: Variable
                                                       └──Variable: t2
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Variable: a9284
                                              └──Type expr: Variable: a9294
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Variable: a9284
                                                       └──Type expr: Variable: a9294
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Refl
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a9284
                                                                └──Type expr: Variable: a9294
                                                 └──Expression:
                                                    └──Type expr: Variable: a9294
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
                └──Variables: a9334
                └──Type expr: Arrow
                   └──Type expr: Constructor: string
                   └──Type expr: Variable: a9334
             └──Primitive name: %fail_with
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: heval
                └──Abstraction:
                   └──Variables: a9343
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: hterm
                            └──Type expr: Variable: a9360
                         └──Type expr: Variable: a9360
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: hterm
                               └──Type expr: Variable: a9360
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Variable: a9360
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: hterm
                                     └──Type expr: Variable: a9360
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: hterm
                                  └──Type expr: Variable: a9360
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: a9360
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Tag
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a9360
                                                    └──Type expr: Constructor: int
                                              └──Constructor type:
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: a9360
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a9360
                                                 └──Type expr: Constructor: int
                                              └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Variable: a9360
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: string
                                                 └──Type expr: Variable: a9360
                                              └──Desc: Variable
                                                 └──Variable: fail_with
                                                 └──Type expr: Variable: a9360
                                           └──Expression:
                                              └──Type expr: Constructor: string
                                              └──Desc: Constant: HOAS eval
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: a9360
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Con
                                              └──Constructor argument type:
                                                 └──Type expr: Variable: a9360
                                              └──Constructor type:
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: a9360
                                           └──Pattern:
                                              └──Type expr: Variable: a9360
                                              └──Desc: Variable: v
                                     └──Expression:
                                        └──Type expr: Variable: a9360
                                        └──Desc: Variable
                                           └──Variable: v
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: a9360
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Lam
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a9409
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a9409
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a9405
                                              └──Constructor type:
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: a9360
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a9409
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: a9409
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: a9405
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a9409
                                                    └──Desc: Any
                                                 └──Pattern:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a9409
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a9405
                                                    └──Desc: Variable: f
                                     └──Expression:
                                        └──Type expr: Variable: a9360
                                        └──Desc: Function
                                           └──Pattern:
                                              └──Type expr: Variable: a9409
                                              └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Variable: a9405
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a9405
                                                       └──Type expr: Variable: a9405
                                                    └──Desc: Variable
                                                       └──Variable: heval
                                                       └──Type expr: Variable: a9405
                                                 └──Expression:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: a9405
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: a9409
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: a9405
                                                          └──Desc: Variable
                                                             └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: a9409
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Con
                                                                └──Constructor argument type:
                                                                   └──Type expr: Variable: a9409
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: hterm
                                                                      └──Type expr: Variable: a9409
                                                             └──Expression:
                                                                └──Type expr: Variable: a9409
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: a9360
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: App
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: a9457
                                                          └──Type expr: Variable: a9360
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: a9457
                                              └──Constructor type:
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: a9360
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: a9457
                                                       └──Type expr: Variable: a9360
                                                 └──Type expr: Constructor: hterm
                                                    └──Type expr: Variable: a9457
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: a9457
                                                          └──Type expr: Variable: a9360
                                                    └──Desc: Variable: f
                                                 └──Pattern:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: a9457
                                                    └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: a9360
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: a9457
                                                 └──Type expr: Variable: a9360
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a9457
                                                             └──Type expr: Variable: a9360
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: a9457
                                                          └──Type expr: Variable: a9360
                                                    └──Desc: Variable
                                                       └──Variable: heval
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: a9457
                                                          └──Type expr: Variable: a9360
                                                 └──Expression:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: a9457
                                                          └──Type expr: Variable: a9360
                                                    └──Desc: Variable
                                                       └──Variable: f
                                           └──Expression:
                                              └──Type expr: Variable: a9457
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a9457
                                                       └──Type expr: Variable: a9457
                                                    └──Desc: Variable
                                                       └──Variable: heval
                                                       └──Type expr: Variable: a9457
                                                 └──Expression:
                                                    └──Type expr: Constructor: hterm
                                                       └──Type expr: Variable: a9457
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
                   └──Variables: a9494,a9493
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: index
                            └──Type expr: Variable: a9515
                            └──Type expr: Variable: a9516
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: index
                               └──Type expr: Variable: a9515
                               └──Type expr: Variable: a9516
                            └──Desc: Variable: ix
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: index
                                     └──Type expr: Variable: a9515
                                     └──Type expr: Variable: a9516
                                  └──Desc: Variable
                                     └──Variable: ix
                               └──Type expr: Constructor: index
                                  └──Type expr: Variable: a9515
                                  └──Type expr: Variable: a9516
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: index
                                           └──Type expr: Variable: a9515
                                           └──Type expr: Variable: a9516
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Zero
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: a9515
                                                    └──Type expr: Variable: a9516
                                           └──Pattern:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 0
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: index
                                           └──Type expr: Variable: a9515
                                           └──Type expr: Variable: a9516
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: a9545
                                                    └──Type expr: Variable: a9516
                                              └──Constructor type:
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: a9515
                                                    └──Type expr: Variable: a9516
                                           └──Pattern:
                                              └──Type expr: Constructor: index
                                                 └──Type expr: Variable: a9545
                                                 └──Type expr: Variable: a9516
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
                                                                └──Type expr: Variable: a9545
                                                                └──Type expr: Variable: a9516
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: index_to_int
                                                             └──Type expr: Variable: a9516
                                                             └──Type expr: Variable: a9545
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: a9545
                                                             └──Type expr: Variable: a9516
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
                   └──Variables: a9594,a9593
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: index
                            └──Type expr: Variable: a9619
                            └──Type expr: Variable: a9620
                         └──Type expr: Arrow
                            └──Type expr: Constructor: stack
                               └──Type expr: Variable: a9619
                            └──Type expr: Variable: a9620
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: index
                               └──Type expr: Variable: a9619
                               └──Type expr: Variable: a9620
                            └──Desc: Variable: ix
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: stack
                                  └──Type expr: Variable: a9619
                               └──Type expr: Variable: a9620
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: stack
                                     └──Type expr: Variable: a9619
                                  └──Desc: Variable: s
                               └──Expression:
                                  └──Type expr: Variable: a9620
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: index
                                              └──Type expr: Variable: a9619
                                              └──Type expr: Variable: a9620
                                           └──Type expr: Constructor: stack
                                              └──Type expr: Variable: a9619
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: index
                                                 └──Type expr: Variable: a9619
                                                 └──Type expr: Variable: a9620
                                              └──Desc: Variable
                                                 └──Variable: ix
                                           └──Expression:
                                              └──Type expr: Constructor: stack
                                                 └──Type expr: Variable: a9619
                                              └──Desc: Variable
                                                 └──Variable: s
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: index
                                           └──Type expr: Variable: a9619
                                           └──Type expr: Variable: a9620
                                        └──Type expr: Constructor: stack
                                           └──Type expr: Variable: a9619
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: a9619
                                                    └──Type expr: Variable: a9620
                                                 └──Type expr: Constructor: stack
                                                    └──Type expr: Variable: a9619
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a9619
                                                       └──Type expr: Variable: a9620
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a9619
                                                                └──Type expr: Variable: a9620
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                                 └──Pattern:
                                                    └──Type expr: Constructor: stack
                                                       └──Type expr: Variable: a9619
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Push
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: a9657
                                                                └──Type expr: Variable: a9655
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: a9619
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: a9657
                                                             └──Type expr: Variable: a9655
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: a9657
                                                                └──Desc: Any
                                                             └──Pattern:
                                                                └──Type expr: Variable: a9655
                                                                └──Desc: Variable: v
                                           └──Expression:
                                              └──Type expr: Variable: a9620
                                              └──Desc: Variable
                                                 └──Variable: v
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: a9619
                                                    └──Type expr: Variable: a9620
                                                 └──Type expr: Constructor: stack
                                                    └──Type expr: Variable: a9619
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a9619
                                                       └──Type expr: Variable: a9620
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a9695
                                                                └──Type expr: Variable: a9620
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a9619
                                                                └──Type expr: Variable: a9620
                                                       └──Pattern:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: a9695
                                                             └──Type expr: Variable: a9620
                                                          └──Desc: Variable: ix
                                                 └──Pattern:
                                                    └──Type expr: Constructor: stack
                                                       └──Type expr: Variable: a9619
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Push
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: a9692
                                                                └──Type expr: Variable: a9690
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: a9619
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: a9692
                                                             └──Type expr: Variable: a9690
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: a9692
                                                                └──Desc: Variable: s
                                                             └──Pattern:
                                                                └──Type expr: Variable: a9690
                                                                └──Desc: Any
                                           └──Expression:
                                              └──Type expr: Variable: a9620
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: stack
                                                          └──Type expr: Variable: a9692
                                                       └──Type expr: Variable: a9620
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a9692
                                                                └──Type expr: Variable: a9620
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: a9692
                                                                └──Type expr: Variable: a9620
                                                          └──Desc: Variable
                                                             └──Variable: prj
                                                             └──Type expr: Variable: a9620
                                                             └──Type expr: Variable: a9692
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: a9692
                                                             └──Type expr: Variable: a9620
                                                          └──Desc: Variable
                                                             └──Variable: ix
                                                 └──Expression:
                                                    └──Type expr: Constructor: stack
                                                       └──Type expr: Variable: a9692
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
                   └──Variables: a9740,a9739
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: dterm
                            └──Type expr: Variable: a9765
                            └──Type expr: Variable: a9766
                         └──Type expr: Arrow
                            └──Type expr: Constructor: stack
                               └──Type expr: Variable: a9765
                            └──Type expr: Variable: a9766
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: dterm
                               └──Type expr: Variable: a9765
                               └──Type expr: Variable: a9766
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: stack
                                  └──Type expr: Variable: a9765
                               └──Type expr: Variable: a9766
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: stack
                                     └──Type expr: Variable: a9765
                                  └──Desc: Variable: s
                               └──Expression:
                                  └──Type expr: Variable: a9766
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: dterm
                                           └──Type expr: Variable: a9765
                                           └──Type expr: Variable: a9766
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Constructor: dterm
                                        └──Type expr: Variable: a9765
                                        └──Type expr: Variable: a9766
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a9765
                                                 └──Type expr: Variable: a9766
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: index
                                                          └──Type expr: Variable: a9765
                                                          └──Type expr: Variable: a9766
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a9765
                                                          └──Type expr: Variable: a9766
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a9765
                                                       └──Type expr: Variable: a9766
                                                    └──Desc: Variable: ix
                                           └──Expression:
                                              └──Type expr: Variable: a9766
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: stack
                                                          └──Type expr: Variable: a9765
                                                       └──Type expr: Variable: a9766
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a9765
                                                                └──Type expr: Variable: a9766
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: stack
                                                                   └──Type expr: Variable: a9765
                                                                └──Type expr: Variable: a9766
                                                          └──Desc: Variable
                                                             └──Variable: prj
                                                             └──Type expr: Variable: a9766
                                                             └──Type expr: Variable: a9765
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: a9765
                                                             └──Type expr: Variable: a9766
                                                          └──Desc: Variable
                                                             └──Variable: ix
                                                 └──Expression:
                                                    └──Type expr: Constructor: stack
                                                       └──Type expr: Variable: a9765
                                                    └──Desc: Variable
                                                       └──Variable: s
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a9765
                                                 └──Type expr: Variable: a9766
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_con
                                                    └──Constructor argument type:
                                                       └──Type expr: Variable: a9766
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a9765
                                                          └──Type expr: Variable: a9766
                                                 └──Pattern:
                                                    └──Type expr: Variable: a9766
                                                    └──Desc: Variable: v
                                           └──Expression:
                                              └──Type expr: Variable: a9766
                                              └──Desc: Variable
                                                 └──Variable: v
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a9765
                                                 └──Type expr: Variable: a9766
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_lam
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a9765
                                                             └──Type expr: Variable: a9823
                                                          └──Type expr: Variable: a9821
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a9765
                                                          └──Type expr: Variable: a9766
                                                 └──Pattern:
                                                    └──Type expr: Constructor: dterm
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a9765
                                                          └──Type expr: Variable: a9823
                                                       └──Type expr: Variable: a9821
                                                    └──Desc: Variable: b
                                           └──Expression:
                                              └──Type expr: Variable: a9766
                                              └──Desc: Function
                                                 └──Pattern:
                                                    └──Type expr: Variable: a9823
                                                    └──Desc: Variable: x
                                                 └──Expression:
                                                    └──Type expr: Variable: a9821
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a9765
                                                                   └──Type expr: Variable: a9823
                                                             └──Type expr: Variable: a9821
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a9765
                                                                         └──Type expr: Variable: a9823
                                                                      └──Type expr: Variable: a9821
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a9765
                                                                            └──Type expr: Variable: a9823
                                                                      └──Type expr: Variable: a9821
                                                                └──Desc: Variable
                                                                   └──Variable: deval
                                                                   └──Type expr: Variable: a9821
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a9765
                                                                      └──Type expr: Variable: a9823
                                                             └──Expression:
                                                                └──Type expr: Constructor: dterm
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a9765
                                                                      └──Type expr: Variable: a9823
                                                                   └──Type expr: Variable: a9821
                                                                └──Desc: Variable
                                                                   └──Variable: b
                                                       └──Expression:
                                                          └──Type expr: Constructor: stack
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a9765
                                                                └──Type expr: Variable: a9823
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Push
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Variable: a9765
                                                                      └──Type expr: Variable: a9823
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: stack
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a9765
                                                                         └──Type expr: Variable: a9823
                                                             └──Expression:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: stack
                                                                      └──Type expr: Variable: a9765
                                                                   └──Type expr: Variable: a9823
                                                                └──Desc: Tuple
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Variable: a9765
                                                                      └──Desc: Variable
                                                                         └──Variable: s
                                                                   └──Expression:
                                                                      └──Type expr: Variable: a9823
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a9765
                                                 └──Type expr: Variable: a9766
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_app
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a9765
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a9886
                                                                └──Type expr: Variable: a9766
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a9765
                                                             └──Type expr: Variable: a9886
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a9765
                                                          └──Type expr: Variable: a9766
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a9765
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a9886
                                                             └──Type expr: Variable: a9766
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a9765
                                                          └──Type expr: Variable: a9886
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a9765
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a9886
                                                                └──Type expr: Variable: a9766
                                                          └──Desc: Variable: f
                                                       └──Pattern:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a9765
                                                             └──Type expr: Variable: a9886
                                                          └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Variable: a9766
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: a9886
                                                       └──Type expr: Variable: a9766
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: a9765
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a9886
                                                                └──Type expr: Variable: a9766
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Variable: a9765
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: a9886
                                                                         └──Type expr: Variable: a9766
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Variable: a9765
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: a9886
                                                                         └──Type expr: Variable: a9766
                                                                └──Desc: Variable
                                                                   └──Variable: deval
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a9886
                                                                      └──Type expr: Variable: a9766
                                                                   └──Type expr: Variable: a9765
                                                             └──Expression:
                                                                └──Type expr: Constructor: dterm
                                                                   └──Type expr: Variable: a9765
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a9886
                                                                      └──Type expr: Variable: a9766
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Constructor: stack
                                                             └──Type expr: Variable: a9765
                                                          └──Desc: Variable
                                                             └──Variable: s
                                                 └──Expression:
                                                    └──Type expr: Variable: a9886
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: stack
                                                                └──Type expr: Variable: a9765
                                                             └──Type expr: Variable: a9886
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Variable: a9765
                                                                      └──Type expr: Variable: a9886
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: stack
                                                                         └──Type expr: Variable: a9765
                                                                      └──Type expr: Variable: a9886
                                                                └──Desc: Variable
                                                                   └──Variable: deval
                                                                   └──Type expr: Variable: a9886
                                                                   └──Type expr: Variable: a9765
                                                             └──Expression:
                                                                └──Type expr: Constructor: dterm
                                                                   └──Type expr: Variable: a9765
                                                                   └──Type expr: Variable: a9886
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: stack
                                                             └──Type expr: Variable: a9765
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
                   └──Variables: a9940,a9939
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: layout
                            └──Type expr: Variable: a9961
                            └──Type expr: Variable: a9962
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: layout
                               └──Type expr: Variable: a9961
                               └──Type expr: Variable: a9962
                            └──Desc: Variable: l
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: layout
                                     └──Type expr: Variable: a9961
                                     └──Type expr: Variable: a9962
                                  └──Desc: Variable
                                     └──Variable: l
                               └──Type expr: Constructor: layout
                                  └──Type expr: Variable: a9961
                                  └──Type expr: Variable: a9962
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: a9961
                                           └──Type expr: Variable: a9962
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Empty_layout
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: a9961
                                                    └──Type expr: Variable: a9962
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 0
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: a9961
                                           └──Type expr: Variable: a9962
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Push_layout
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a9997
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: a9961
                                                       └──Type expr: Variable: a9995
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a9961
                                                       └──Type expr: Variable: a9997
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: a9961
                                                    └──Type expr: Variable: a9962
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a9997
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: a9961
                                                    └──Type expr: Variable: a9995
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: a9961
                                                    └──Type expr: Variable: a9997
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a9997
                                                    └──Desc: Any
                                                 └──Pattern:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: a9961
                                                       └──Type expr: Variable: a9995
                                                    └──Desc: Variable: l
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a9961
                                                       └──Type expr: Variable: a9997
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
                                                                └──Type expr: Variable: a9961
                                                                └──Type expr: Variable: a9995
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: size
                                                             └──Type expr: Variable: a9995
                                                             └──Type expr: Variable: a9961
                                                       └──Expression:
                                                          └──Type expr: Constructor: layout
                                                             └──Type expr: Variable: a9961
                                                             └──Type expr: Variable: a9995
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
                   └──Variables: a10046,a10049,a10048
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: layout
                            └──Type expr: Variable: a10076
                            └──Type expr: Variable: a10077
                         └──Type expr: Constructor: layout
                            └──Type expr: Tuple
                               └──Type expr: Variable: a10076
                               └──Type expr: Variable: a10108
                            └──Type expr: Variable: a10077
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: layout
                               └──Type expr: Variable: a10076
                               └──Type expr: Variable: a10077
                            └──Desc: Variable: l
                         └──Expression:
                            └──Type expr: Constructor: layout
                               └──Type expr: Tuple
                                  └──Type expr: Variable: a10076
                                  └──Type expr: Variable: a10108
                               └──Type expr: Variable: a10077
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: layout
                                     └──Type expr: Variable: a10076
                                     └──Type expr: Variable: a10077
                                  └──Desc: Variable
                                     └──Variable: l
                               └──Type expr: Constructor: layout
                                  └──Type expr: Variable: a10076
                                  └──Type expr: Variable: a10077
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: a10076
                                           └──Type expr: Variable: a10077
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Empty_layout
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: a10076
                                                    └──Type expr: Variable: a10077
                                     └──Expression:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a10076
                                              └──Type expr: Variable: a10108
                                           └──Type expr: Variable: a10077
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Empty_layout
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a10076
                                                       └──Type expr: Variable: a10108
                                                    └──Type expr: Variable: a10077
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: a10076
                                           └──Type expr: Variable: a10077
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Push_layout
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a10138
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: a10076
                                                       └──Type expr: Variable: a10136
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a10076
                                                       └──Type expr: Variable: a10138
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: a10076
                                                    └──Type expr: Variable: a10077
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a10138
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Variable: a10076
                                                    └──Type expr: Variable: a10136
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Variable: a10076
                                                    └──Type expr: Variable: a10138
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a10138
                                                    └──Desc: Variable: t
                                                 └──Pattern:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: a10076
                                                       └──Type expr: Variable: a10136
                                                    └──Desc: Variable: l
                                                 └──Pattern:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a10076
                                                       └──Type expr: Variable: a10138
                                                    └──Desc: Variable: ix
                                     └──Expression:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a10076
                                              └──Type expr: Variable: a10108
                                           └──Type expr: Variable: a10077
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Push_layout
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a10138
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a10076
                                                          └──Type expr: Variable: a10108
                                                       └──Type expr: Variable: a10136
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a10076
                                                          └──Type expr: Variable: a10108
                                                       └──Type expr: Variable: a10138
                                              └──Constructor type:
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a10076
                                                       └──Type expr: Variable: a10108
                                                    └──Type expr: Variable: a10077
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ty
                                                    └──Type expr: Variable: a10138
                                                 └──Type expr: Constructor: layout
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a10076
                                                       └──Type expr: Variable: a10108
                                                    └──Type expr: Variable: a10136
                                                 └──Type expr: Constructor: index
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a10076
                                                       └──Type expr: Variable: a10108
                                                    └──Type expr: Variable: a10138
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: ty
                                                       └──Type expr: Variable: a10138
                                                    └──Desc: Variable
                                                       └──Variable: t
                                                 └──Expression:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a10076
                                                          └──Type expr: Variable: a10108
                                                       └──Type expr: Variable: a10136
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: a10076
                                                                └──Type expr: Variable: a10136
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a10076
                                                                   └──Type expr: Variable: a10108
                                                                └──Type expr: Variable: a10136
                                                          └──Desc: Variable
                                                             └──Variable: inc
                                                             └──Type expr: Variable: a10108
                                                             └──Type expr: Variable: a10136
                                                             └──Type expr: Variable: a10076
                                                       └──Expression:
                                                          └──Type expr: Constructor: layout
                                                             └──Type expr: Variable: a10076
                                                             └──Type expr: Variable: a10136
                                                          └──Desc: Variable
                                                             └──Variable: l
                                                 └──Expression:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a10076
                                                          └──Type expr: Variable: a10108
                                                       └──Type expr: Variable: a10138
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a10076
                                                                └──Type expr: Variable: a10138
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a10076
                                                                   └──Type expr: Variable: a10108
                                                                └──Type expr: Variable: a10138
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: a10076
                                                             └──Type expr: Variable: a10138
                                                          └──Desc: Variable
                                                             └──Variable: ix
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: prjl
                └──Abstraction:
                   └──Variables: a10227,a10226,a10230
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ty
                            └──Type expr: Variable: a10262
                         └──Type expr: Arrow
                            └──Type expr: Constructor: int
                            └──Type expr: Arrow
                               └──Type expr: Constructor: layout
                                  └──Type expr: Variable: a10281
                                  └──Type expr: Variable: a10282
                               └──Type expr: Constructor: index
                                  └──Type expr: Variable: a10281
                                  └──Type expr: Variable: a10262
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ty
                               └──Type expr: Variable: a10262
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: layout
                                     └──Type expr: Variable: a10281
                                     └──Type expr: Variable: a10282
                                  └──Type expr: Constructor: index
                                     └──Type expr: Variable: a10281
                                     └──Type expr: Variable: a10262
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable: n
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: layout
                                        └──Type expr: Variable: a10281
                                        └──Type expr: Variable: a10282
                                     └──Type expr: Constructor: index
                                        └──Type expr: Variable: a10281
                                        └──Type expr: Variable: a10262
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: layout
                                           └──Type expr: Variable: a10281
                                           └──Type expr: Variable: a10282
                                        └──Desc: Variable: l
                                     └──Expression:
                                        └──Type expr: Constructor: index
                                           └──Type expr: Variable: a10281
                                           └──Type expr: Variable: a10262
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: layout
                                                 └──Type expr: Variable: a10281
                                                 └──Type expr: Variable: a10282
                                              └──Desc: Variable
                                                 └──Variable: l
                                           └──Type expr: Constructor: layout
                                              └──Type expr: Variable: a10281
                                              └──Type expr: Variable: a10282
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: a10281
                                                       └──Type expr: Variable: a10282
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Empty_layout
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: a10281
                                                                └──Type expr: Variable: a10282
                                                 └──Expression:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a10281
                                                       └──Type expr: Variable: a10262
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: string
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a10281
                                                                └──Type expr: Variable: a10262
                                                          └──Desc: Variable
                                                             └──Variable: fail_with
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a10281
                                                                └──Type expr: Variable: a10262
                                                       └──Expression:
                                                          └──Type expr: Constructor: string
                                                          └──Desc: Constant: convert prjl
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: layout
                                                       └──Type expr: Variable: a10281
                                                       └──Type expr: Variable: a10282
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Push_layout
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a10331
                                                                └──Type expr: Constructor: layout
                                                                   └──Type expr: Variable: a10281
                                                                   └──Type expr: Variable: a10329
                                                                └──Type expr: Constructor: index
                                                                   └──Type expr: Variable: a10281
                                                                   └──Type expr: Variable: a10331
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: a10281
                                                                └──Type expr: Variable: a10282
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: ty
                                                                └──Type expr: Variable: a10331
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: a10281
                                                                └──Type expr: Variable: a10329
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a10281
                                                                └──Type expr: Variable: a10331
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: ty
                                                                   └──Type expr: Variable: a10331
                                                                └──Desc: Variable: t'
                                                             └──Pattern:
                                                                └──Type expr: Constructor: layout
                                                                   └──Type expr: Variable: a10281
                                                                   └──Type expr: Variable: a10329
                                                                └──Desc: Variable: l
                                                             └──Pattern:
                                                                └──Type expr: Constructor: index
                                                                   └──Type expr: Variable: a10281
                                                                   └──Type expr: Variable: a10331
                                                                └──Desc: Variable: ix
                                                 └──Expression:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a10281
                                                       └──Type expr: Variable: a10262
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
                                                             └──Type expr: Variable: a10281
                                                             └──Type expr: Variable: a10262
                                                          └──Desc: Match
                                                             └──Expression:
                                                                └──Type expr: Constructor: eq
                                                                   └──Type expr: Variable: a10262
                                                                   └──Type expr: Variable: a10331
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a10331
                                                                         └──Type expr: Constructor: eq
                                                                            └──Type expr: Variable: a10262
                                                                            └──Type expr: Variable: a10331
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: ty
                                                                                  └──Type expr: Variable: a10262
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: ty
                                                                                     └──Type expr: Variable: a10331
                                                                                  └──Type expr: Constructor: eq
                                                                                     └──Type expr: Variable: a10262
                                                                                     └──Type expr: Variable: a10331
                                                                            └──Desc: Variable
                                                                               └──Variable: check_eq
                                                                               └──Type expr: Variable: a10331
                                                                               └──Type expr: Variable: a10262
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: a10262
                                                                            └──Desc: Variable
                                                                               └──Variable: t
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a10331
                                                                      └──Desc: Variable
                                                                         └──Variable: t'
                                                             └──Type expr: Constructor: eq
                                                                └──Type expr: Variable: a10262
                                                                └──Type expr: Variable: a10331
                                                             └──Cases:
                                                                └──Case:
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: eq
                                                                         └──Type expr: Variable: a10262
                                                                         └──Type expr: Variable: a10331
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Refl
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: eq
                                                                                  └──Type expr: Variable: a10262
                                                                                  └──Type expr: Variable: a10331
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: index
                                                                         └──Type expr: Variable: a10281
                                                                         └──Type expr: Variable: a10262
                                                                      └──Desc: Variable
                                                                         └──Variable: ix
                                                       └──Expression:
                                                          └──Type expr: Constructor: index
                                                             └──Type expr: Variable: a10281
                                                             └──Type expr: Variable: a10262
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: layout
                                                                      └──Type expr: Variable: a10281
                                                                      └──Type expr: Variable: a10329
                                                                   └──Type expr: Constructor: index
                                                                      └──Type expr: Variable: a10281
                                                                      └──Type expr: Variable: a10262
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: int
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: layout
                                                                               └──Type expr: Variable: a10281
                                                                               └──Type expr: Variable: a10329
                                                                            └──Type expr: Constructor: index
                                                                               └──Type expr: Variable: a10281
                                                                               └──Type expr: Variable: a10262
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: ty
                                                                                  └──Type expr: Variable: a10262
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: int
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: layout
                                                                                        └──Type expr: Variable: a10281
                                                                                        └──Type expr: Variable: a10329
                                                                                     └──Type expr: Constructor: index
                                                                                        └──Type expr: Variable: a10281
                                                                                        └──Type expr: Variable: a10262
                                                                            └──Desc: Variable
                                                                               └──Variable: prjl
                                                                               └──Type expr: Variable: a10329
                                                                               └──Type expr: Variable: a10281
                                                                               └──Type expr: Variable: a10262
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: ty
                                                                               └──Type expr: Variable: a10262
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
                                                                   └──Type expr: Variable: a10281
                                                                   └──Type expr: Variable: a10329
                                                                └──Desc: Variable
                                                                   └──Variable: l
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: convert
                └──Abstraction:
                   └──Variables: a10456,a10459
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: layout
                            └──Type expr: Variable: a10488
                            └──Type expr: Variable: a10488
                         └──Type expr: Arrow
                            └──Type expr: Constructor: hterm
                               └──Type expr: Variable: a10498
                            └──Type expr: Constructor: dterm
                               └──Type expr: Variable: a10488
                               └──Type expr: Variable: a10498
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: layout
                               └──Type expr: Variable: a10488
                               └──Type expr: Variable: a10488
                            └──Desc: Variable: l
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: hterm
                                  └──Type expr: Variable: a10498
                               └──Type expr: Constructor: dterm
                                  └──Type expr: Variable: a10488
                                  └──Type expr: Variable: a10498
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: hterm
                                     └──Type expr: Variable: a10498
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Constructor: dterm
                                     └──Type expr: Variable: a10488
                                     └──Type expr: Variable: a10498
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: hterm
                                           └──Type expr: Variable: a10498
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Constructor: hterm
                                        └──Type expr: Variable: a10498
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: hterm
                                                 └──Type expr: Variable: a10498
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Tag
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a10498
                                                          └──Type expr: Constructor: int
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a10498
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: a10498
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a10498
                                                          └──Desc: Variable: t
                                                       └──Pattern:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable: sz
                                           └──Expression:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a10488
                                                 └──Type expr: Variable: a10498
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: index
                                                          └──Type expr: Variable: a10488
                                                          └──Type expr: Variable: a10498
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a10488
                                                          └──Type expr: Variable: a10498
                                                 └──Expression:
                                                    └──Type expr: Constructor: index
                                                       └──Type expr: Variable: a10488
                                                       └──Type expr: Variable: a10498
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Variable: a10488
                                                                └──Type expr: Variable: a10488
                                                             └──Type expr: Constructor: index
                                                                └──Type expr: Variable: a10488
                                                                └──Type expr: Variable: a10498
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: int
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Variable: a10488
                                                                         └──Type expr: Variable: a10488
                                                                      └──Type expr: Constructor: index
                                                                         └──Type expr: Variable: a10488
                                                                         └──Type expr: Variable: a10498
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a10498
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: int
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: layout
                                                                                  └──Type expr: Variable: a10488
                                                                                  └──Type expr: Variable: a10488
                                                                               └──Type expr: Constructor: index
                                                                                  └──Type expr: Variable: a10488
                                                                                  └──Type expr: Variable: a10498
                                                                      └──Desc: Variable
                                                                         └──Variable: prjl
                                                                         └──Type expr: Variable: a10488
                                                                         └──Type expr: Variable: a10488
                                                                         └──Type expr: Variable: a10498
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a10498
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
                                                                                                    └──Type expr: Variable: a10488
                                                                                                    └──Type expr: Variable: a10488
                                                                                                 └──Type expr: Constructor: int
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: size
                                                                                                 └──Type expr: Variable: a10488
                                                                                                 └──Type expr: Variable: a10488
                                                                                           └──Expression:
                                                                                              └──Type expr: Constructor: layout
                                                                                                 └──Type expr: Variable: a10488
                                                                                                 └──Type expr: Variable: a10488
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
                                                             └──Type expr: Variable: a10488
                                                             └──Type expr: Variable: a10488
                                                          └──Desc: Variable
                                                             └──Variable: l
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: hterm
                                                 └──Type expr: Variable: a10498
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Con
                                                    └──Constructor argument type:
                                                       └──Type expr: Variable: a10498
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a10498
                                                 └──Pattern:
                                                    └──Type expr: Variable: a10498
                                                    └──Desc: Variable: v
                                           └──Expression:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a10488
                                                 └──Type expr: Variable: a10498
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_con
                                                    └──Constructor argument type:
                                                       └──Type expr: Variable: a10498
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a10488
                                                          └──Type expr: Variable: a10498
                                                 └──Expression:
                                                    └──Type expr: Variable: a10498
                                                    └──Desc: Variable
                                                       └──Variable: v
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: hterm
                                                 └──Type expr: Variable: a10498
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Lam
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a10637
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: a10637
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: a10633
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a10498
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: ty
                                                          └──Type expr: Variable: a10637
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: a10637
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: a10633
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ty
                                                             └──Type expr: Variable: a10637
                                                          └──Desc: Variable: t
                                                       └──Pattern:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: a10637
                                                             └──Type expr: Constructor: hterm
                                                                └──Type expr: Variable: a10633
                                                          └──Desc: Variable: f
                                           └──Expression:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a10488
                                                 └──Type expr: Variable: a10498
                                              └──Desc: Let
                                                 └──Value bindings:
                                                    └──Value binding:
                                                       └──Pattern:
                                                          └──Type expr: Constructor: layout
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a10488
                                                                └──Type expr: Variable: a10637
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a10488
                                                                └──Type expr: Variable: a10637
                                                          └──Desc: Variable: l'
                                                       └──Abstraction:
                                                          └──Variables:
                                                          └──Expression:
                                                             └──Type expr: Constructor: layout
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a10488
                                                                   └──Type expr: Variable: a10637
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a10488
                                                                   └──Type expr: Variable: a10637
                                                             └──Desc: Construct
                                                                └──Constructor description:
                                                                   └──Name: Push_layout
                                                                   └──Constructor argument type:
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a10637
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a10488
                                                                               └──Type expr: Variable: a10637
                                                                            └──Type expr: Variable: a10488
                                                                         └──Type expr: Constructor: index
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a10488
                                                                               └──Type expr: Variable: a10637
                                                                            └──Type expr: Variable: a10637
                                                                   └──Constructor type:
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a10488
                                                                            └──Type expr: Variable: a10637
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a10488
                                                                            └──Type expr: Variable: a10637
                                                                └──Expression:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: ty
                                                                         └──Type expr: Variable: a10637
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a10488
                                                                            └──Type expr: Variable: a10637
                                                                         └──Type expr: Variable: a10488
                                                                      └──Type expr: Constructor: index
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a10488
                                                                            └──Type expr: Variable: a10637
                                                                         └──Type expr: Variable: a10637
                                                                   └──Desc: Tuple
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: ty
                                                                            └──Type expr: Variable: a10637
                                                                         └──Desc: Variable
                                                                            └──Variable: t
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a10488
                                                                               └──Type expr: Variable: a10637
                                                                            └──Type expr: Variable: a10488
                                                                         └──Desc: Application
                                                                            └──Expression:
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: layout
                                                                                     └──Type expr: Variable: a10488
                                                                                     └──Type expr: Variable: a10488
                                                                                  └──Type expr: Constructor: layout
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Variable: a10488
                                                                                        └──Type expr: Variable: a10637
                                                                                     └──Type expr: Variable: a10488
                                                                               └──Desc: Variable
                                                                                  └──Variable: inc
                                                                                  └──Type expr: Variable: a10637
                                                                                  └──Type expr: Variable: a10488
                                                                                  └──Type expr: Variable: a10488
                                                                            └──Expression:
                                                                               └──Type expr: Constructor: layout
                                                                                  └──Type expr: Variable: a10488
                                                                                  └──Type expr: Variable: a10488
                                                                               └──Desc: Variable
                                                                                  └──Variable: l
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: index
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a10488
                                                                               └──Type expr: Variable: a10637
                                                                            └──Type expr: Variable: a10637
                                                                         └──Desc: Construct
                                                                            └──Constructor description:
                                                                               └──Name: Zero
                                                                               └──Constructor argument type:
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Constructor type:
                                                                                  └──Type expr: Constructor: index
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Variable: a10488
                                                                                        └──Type expr: Variable: a10637
                                                                                     └──Type expr: Variable: a10637
                                                                            └──Expression:
                                                                               └──Type expr: Constructor: unit
                                                                               └──Desc: Constant: ()
                                                 └──Expression:
                                                    └──Type expr: Constructor: dterm
                                                       └──Type expr: Variable: a10488
                                                       └──Type expr: Variable: a10498
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: D_lam
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: dterm
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a10488
                                                                   └──Type expr: Variable: a10637
                                                                └──Type expr: Variable: a10633
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: dterm
                                                                └──Type expr: Variable: a10488
                                                                └──Type expr: Variable: a10498
                                                       └──Expression:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a10488
                                                                └──Type expr: Variable: a10637
                                                             └──Type expr: Variable: a10633
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: hterm
                                                                      └──Type expr: Variable: a10633
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a10488
                                                                         └──Type expr: Variable: a10637
                                                                      └──Type expr: Variable: a10633
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a10488
                                                                               └──Type expr: Variable: a10637
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a10488
                                                                               └──Type expr: Variable: a10637
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: hterm
                                                                               └──Type expr: Variable: a10633
                                                                            └──Type expr: Constructor: dterm
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: a10488
                                                                                  └──Type expr: Variable: a10637
                                                                               └──Type expr: Variable: a10633
                                                                      └──Desc: Variable
                                                                         └──Variable: convert
                                                                         └──Type expr: Variable: a10633
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a10488
                                                                            └──Type expr: Variable: a10637
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a10488
                                                                            └──Type expr: Variable: a10637
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a10488
                                                                            └──Type expr: Variable: a10637
                                                                      └──Desc: Variable
                                                                         └──Variable: l'
                                                             └──Expression:
                                                                └──Type expr: Constructor: hterm
                                                                   └──Type expr: Variable: a10633
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: hterm
                                                                            └──Type expr: Variable: a10637
                                                                         └──Type expr: Constructor: hterm
                                                                            └──Type expr: Variable: a10633
                                                                      └──Desc: Variable
                                                                         └──Variable: f
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: hterm
                                                                         └──Type expr: Variable: a10637
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Tag
                                                                            └──Constructor argument type:
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Constructor: ty
                                                                                     └──Type expr: Variable: a10637
                                                                                  └──Type expr: Constructor: int
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: hterm
                                                                                  └──Type expr: Variable: a10637
                                                                         └──Expression:
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Constructor: ty
                                                                                  └──Type expr: Variable: a10637
                                                                               └──Type expr: Constructor: int
                                                                            └──Desc: Tuple
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: ty
                                                                                     └──Type expr: Variable: a10637
                                                                                  └──Desc: Variable
                                                                                     └──Variable: t
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: int
                                                                                  └──Desc: Application
                                                                                     └──Expression:
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Constructor: layout
                                                                                              └──Type expr: Variable: a10488
                                                                                              └──Type expr: Variable: a10488
                                                                                           └──Type expr: Constructor: int
                                                                                        └──Desc: Variable
                                                                                           └──Variable: size
                                                                                           └──Type expr: Variable: a10488
                                                                                           └──Type expr: Variable: a10488
                                                                                     └──Expression:
                                                                                        └──Type expr: Constructor: layout
                                                                                           └──Type expr: Variable: a10488
                                                                                           └──Type expr: Variable: a10488
                                                                                        └──Desc: Variable
                                                                                           └──Variable: l
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: hterm
                                                 └──Type expr: Variable: a10498
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: App
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a10775
                                                                └──Type expr: Variable: a10498
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: a10775
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a10498
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a10775
                                                             └──Type expr: Variable: a10498
                                                       └──Type expr: Constructor: hterm
                                                          └──Type expr: Variable: a10775
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a10775
                                                                └──Type expr: Variable: a10498
                                                          └──Desc: Variable: f
                                                       └──Pattern:
                                                          └──Type expr: Constructor: hterm
                                                             └──Type expr: Variable: a10775
                                                          └──Desc: Variable: a
                                           └──Expression:
                                              └──Type expr: Constructor: dterm
                                                 └──Type expr: Variable: a10488
                                                 └──Type expr: Variable: a10498
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: D_app
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a10488
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a10775
                                                                └──Type expr: Variable: a10498
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a10488
                                                             └──Type expr: Variable: a10775
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a10488
                                                          └──Type expr: Variable: a10498
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a10488
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a10775
                                                             └──Type expr: Variable: a10498
                                                       └──Type expr: Constructor: dterm
                                                          └──Type expr: Variable: a10488
                                                          └──Type expr: Variable: a10775
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a10488
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a10775
                                                                └──Type expr: Variable: a10498
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: hterm
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: a10775
                                                                         └──Type expr: Variable: a10498
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Variable: a10488
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: a10775
                                                                         └──Type expr: Variable: a10498
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Variable: a10488
                                                                            └──Type expr: Variable: a10488
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: hterm
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: a10775
                                                                                  └──Type expr: Variable: a10498
                                                                            └──Type expr: Constructor: dterm
                                                                               └──Type expr: Variable: a10488
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: a10775
                                                                                  └──Type expr: Variable: a10498
                                                                      └──Desc: Variable
                                                                         └──Variable: convert
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Variable: a10775
                                                                            └──Type expr: Variable: a10498
                                                                         └──Type expr: Variable: a10488
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Variable: a10488
                                                                         └──Type expr: Variable: a10488
                                                                      └──Desc: Variable
                                                                         └──Variable: l
                                                             └──Expression:
                                                                └──Type expr: Constructor: hterm
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a10775
                                                                      └──Type expr: Variable: a10498
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Constructor: dterm
                                                             └──Type expr: Variable: a10488
                                                             └──Type expr: Variable: a10775
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: hterm
                                                                      └──Type expr: Variable: a10775
                                                                   └──Type expr: Constructor: dterm
                                                                      └──Type expr: Variable: a10488
                                                                      └──Type expr: Variable: a10775
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: layout
                                                                            └──Type expr: Variable: a10488
                                                                            └──Type expr: Variable: a10488
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: hterm
                                                                               └──Type expr: Variable: a10775
                                                                            └──Type expr: Constructor: dterm
                                                                               └──Type expr: Variable: a10488
                                                                               └──Type expr: Variable: a10775
                                                                      └──Desc: Variable
                                                                         └──Variable: convert
                                                                         └──Type expr: Variable: a10775
                                                                         └──Type expr: Variable: a10488
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: layout
                                                                         └──Type expr: Variable: a10488
                                                                         └──Type expr: Variable: a10488
                                                                      └──Desc: Variable
                                                                         └──Variable: l
                                                             └──Expression:
                                                                └──Type expr: Constructor: hterm
                                                                   └──Type expr: Variable: a10775
                                                                └──Desc: Variable
                                                                   └──Variable: a |}]