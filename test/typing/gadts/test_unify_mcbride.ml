open! Import
open Util

let%expect_test "unify-mcbride" =
  let str = 
    {|
      type zero;;
      type 'n succ;;

      type 'n nat = 
        | Zero constraint 'n = zero
        | Succ of 'n1. 'n1 nat constraint 'n = 'n1 succ
      ;;

      type 'n fin =
        | Fin_zero of 'n1. unit constraint 'n = 'n1 succ
        | Fin_succ of 'n1. 'n1 fin constraint 'n = 'n1 succ
      ;;

      type 'n is_succ = 
        | Is_succ of 'n1. unit constraint 'n = 'n1 succ
      ;;

      let (type 'n) fin_succ = 
        fun (f : 'n fin) ->
          (match f with
           ( Fin_zero () -> Is_succ ()
           | Fin_succ _ -> Is_succ ()
           ) 
          : 'n is_succ)
      ;;

      type 'n term = 
        | Var of 'n fin
        | Leaf
        | Fork of 'n term * 'n term
      ;;
      
      let var = fun x -> Var x;;

      let lift = 
        exists (type 'm 'n) ->
        fun r -> (fun x -> Var (r x) : 'm fin -> 'n term)
      ;;

      let rec pre_subst = 
        fun f t ->
          match t with
          ( Var x -> f x
          | Leaf -> Leaf
          | Fork (t1, t2) -> Fork (pre_subst f t1, pre_subst f t2)
          )
      ;;

      let comp_subst = 
        exists (type 'a) ->
        fun f g (x : 'a fin) -> 
          pre_subst f (g x)
      ;;

      let rec (type 'n) thin = 
        fun (x : 'n succ fin) (y : 'n fin) ->
          (match (x, y) with 
           ( (Fin_zero (), y) -> Fin_succ y
           | (Fin_succ x, Fin_zero ()) -> Fin_zero ()
           | (Fin_succ x, Fin_succ y) -> Fin_succ (thin x y) 
           )
          : 'n succ fin)
      ;;

      type 'a option = 
        | None
        | Some of 'a
      ;;

      let bind = 
        fun t f ->
          match t with
          ( None -> None
          | Some x -> f x
          )
      ;;

      let rec (type 'n) thick = 
        fun (x : 'n succ fin) (y : 'n succ fin) ->
          (match (x, y) with
           ( (Fin_zero (), Fin_zero ()) -> None
           | (Fin_zero (), Fin_succ y) -> Some y
           | (Fin_succ x, Fin_zero ()) -> match fin_succ x with ( Is_succ () -> Some (Fin_zero ())) 
           | (Fin_succ x, Fin_succ y) ->
              match fin_succ x with
                ( Is_succ () -> bind (thick x y) (fun x -> Some (Fin_succ x)) ) 
           ) 
          : 'n fin option) 
      ;;

      let rec (type 'n) check = 
        fun (x : 'n succ fin) (t : 'n succ term) ->
          (match t with
           ( Var y -> bind (thick x y) (fun x -> Some (Var x))
           | Leaf -> Some Leaf
           | Fork (t1, t2) ->
              bind (check x t1) (fun t1 ->
                bind (check x t2) (fun t2 -> Some (Fork (t1, t2)))) 
           )
          : 'n term option)
      ;;

      let subst_var = 
        fun x t' y ->
          match thick x y with
          ( None -> t'
          | Some y' -> Var y'
          )
      ;;

      let subst = fun x t' -> pre_subst (subst_var x t');;

      type ('m, 'n) alist = 
        | Anil constraint 'm = 'n
        | Asnoc of 'm1. ('m1, 'n) alist * 'm1 term * 'm1 succ fin constraint 'm = 'm1 succ
      ;;

      let rec (type 'm 'n) sub = 
        fun (s : ('m, 'n) alist) ->
          (match s with 
           ( Anil -> var
           | Asnoc (s, t, x) -> comp_subst (sub s) (subst_var x t)
           )
          : 'm fin -> 'n term)
      ;; 

      let rec (type 'l 'm 'n) append = 
        fun (s1 : ('m, 'n) alist) (s2 : ('l, 'm) alist) ->
          (match s2 with
           ( Anil -> s1
           | Asnoc (s2, t, x) -> Asnoc (append s1 s2, t, x)
           ) 
          : ('l, 'n) alist)
      ;;

      type 'm ex_alist = 
        | Exists_alist of 'n. ('m, 'n) alist
      ;;

      let asnoc = fun a t x -> Exists_alist (Asnoc (a, t, x));; 

      let rec (type 'n) weaken_fin = 
        fun (f : 'n fin) ->
          (match f with 
           ( Fin_zero () -> Fin_zero ()
           | Fin_succ f -> Fin_succ (weaken_fin f)
           )
          : 'n succ fin)
      ;;

      let weaken_term = fun t -> pre_subst (fun x -> Var (weaken_fin x)) t;;

      let rec (type 'm 'n) weaken_alist =
        fun (s : ('m, 'n) alist) ->
          (match s with
           ( Anil -> Anil
           | Asnoc (s, t, x) -> Asnoc (weaken_alist s, weaken_term t, weaken_fin x)
           ) 
          : ('m succ, 'n succ) alist)
      ;;

      let rec (type 'm) sub' = 
        fun (e : 'm ex_alist) ->
          (match e with
           ( Exists_alist Anil -> var
           | Exists_alist (Asnoc (s, t, x)) ->
               comp_subst (sub' (Exists_alist (weaken_alist s)))
                (fun t' -> weaken_term (subst_var x t t'))
           )
          : 'm fin -> 'm term)
      ;;

      let subst' = fun e -> pre_subst (sub' e);;

      let flex_flex = 
        fun x y -> 
          match thick x y with
          ( Some y' -> asnoc Anil (Var y') x
          | None -> Exists_alist Anil
          )
      ;;
      
      let flex_rigid = 
        fun x t -> 
          bind (check x t) (fun t' -> Some (asnoc Anil t' x))
      ;;

      let rec (type 'm) amgu = 
        fun (s : 'm term) (t : 'm term) (acc : 'm ex_alist) ->
          (match (s, t, acc) with 
           ( (Leaf, Leaf, _) -> Some acc 
           | (Leaf, Fork _, _) -> None
           | (Fork _, Leaf, _) -> None
           | (Fork (s1, s2), Fork (t1, t2), _) ->
                bind (amgu s1 t1 acc) (amgu s2 t2)
           )
          : 'm ex_alist option)
      ;;

      let mgu = fun s t -> amgu s t (Exists_alist Anil);;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: zero
             └──Type declaration kind: Abstract
       └──Structure item: Type
          └──Type declaration:
             └──Type name: succ
             └──Type declaration kind: Abstract
       └──Structure item: Type
          └──Type declaration:
             └──Type name: nat
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Zero
                   └──Constructor alphas: n
                   └──Constructor type:
                      └──Type expr: Constructor: nat
                         └──Type expr: Variable: n
                   └──Constraint:
                      └──Type expr: Variable: n
                      └──Type expr: Constructor: zero
                └──Constructor declaration:
                   └──Constructor name: Succ
                   └──Constructor alphas: n
                   └──Constructor type:
                      └──Type expr: Constructor: nat
                         └──Type expr: Variable: n
                   └──Constructor argument:
                      └──Constructor betas: n1
                      └──Type expr: Constructor: nat
                         └──Type expr: Variable: n1
                   └──Constraint:
                      └──Type expr: Variable: n
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: n1
       └──Structure item: Type
          └──Type declaration:
             └──Type name: fin
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Fin_zero
                   └──Constructor alphas: n
                   └──Constructor type:
                      └──Type expr: Constructor: fin
                         └──Type expr: Variable: n
                   └──Constructor argument:
                      └──Constructor betas: n1
                      └──Type expr: Constructor: unit
                   └──Constraint:
                      └──Type expr: Variable: n
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: n1
                └──Constructor declaration:
                   └──Constructor name: Fin_succ
                   └──Constructor alphas: n
                   └──Constructor type:
                      └──Type expr: Constructor: fin
                         └──Type expr: Variable: n
                   └──Constructor argument:
                      └──Constructor betas: n1
                      └──Type expr: Constructor: fin
                         └──Type expr: Variable: n1
                   └──Constraint:
                      └──Type expr: Variable: n
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: n1
       └──Structure item: Type
          └──Type declaration:
             └──Type name: is_succ
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Is_succ
                   └──Constructor alphas: n
                   └──Constructor type:
                      └──Type expr: Constructor: is_succ
                         └──Type expr: Variable: n
                   └──Constructor argument:
                      └──Constructor betas: n1
                      └──Type expr: Constructor: unit
                   └──Constraint:
                      └──Type expr: Variable: n
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: n1
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: fin
                         └──Type expr: Variable: a7227
                      └──Type expr: Constructor: is_succ
                         └──Type expr: Variable: a7227
                   └──Desc: Variable: fin_succ
                └──Abstraction:
                   └──Variables: a7227
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: a7227
                         └──Type expr: Constructor: is_succ
                            └──Type expr: Variable: a7227
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a7227
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Constructor: is_succ
                               └──Type expr: Variable: a7227
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: a7227
                                  └──Desc: Variable
                                     └──Variable: f
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a7227
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: a7227
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_zero
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a7227
                                           └──Pattern:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
                                     └──Expression:
                                        └──Type expr: Constructor: is_succ
                                           └──Type expr: Variable: a7227
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Is_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: is_succ
                                                    └──Type expr: Variable: a7227
                                           └──Expression:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: a7227
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a7268
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a7227
                                           └──Pattern:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: a7268
                                              └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Constructor: is_succ
                                           └──Type expr: Variable: a7227
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Is_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: is_succ
                                                    └──Type expr: Variable: a7227
                                           └──Expression:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
       └──Structure item: Type
          └──Type declaration:
             └──Type name: term
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Var
                   └──Constructor alphas: n
                   └──Constructor type:
                      └──Type expr: Constructor: term
                         └──Type expr: Variable: n
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: fin
                         └──Type expr: Variable: n
                └──Constructor declaration:
                   └──Constructor name: Leaf
                   └──Constructor alphas: n
                   └──Constructor type:
                      └──Type expr: Constructor: term
                         └──Type expr: Variable: n
                └──Constructor declaration:
                   └──Constructor name: Fork
                   └──Constructor alphas: n
                   └──Constructor type:
                      └──Type expr: Constructor: term
                         └──Type expr: Variable: n
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: n
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: n
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: fin
                         └──Type expr: Variable: a7297
                      └──Type expr: Constructor: term
                         └──Type expr: Variable: a7297
                   └──Desc: Variable: var
                └──Abstraction:
                   └──Variables: a7297
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: a7297
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a7297
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a7297
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a7297
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Var
                                  └──Constructor argument type:
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Variable: a7297
                                  └──Constructor type:
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: a7297
                               └──Expression:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: a7297
                                  └──Desc: Variable
                                     └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: a7303
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: a7325
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: a7303
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a7325
                   └──Desc: Variable: lift
                └──Abstraction:
                   └──Variables: a7325,a7325,a7303
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a7303
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a7325
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a7303
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a7325
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a7303
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a7325
                            └──Desc: Variable: r
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a7303
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a7325
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: a7303
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a7325
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Var
                                        └──Constructor argument type:
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: a7325
                                        └──Constructor type:
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: a7325
                                     └──Expression:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: a7325
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a7303
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a7325
                                              └──Desc: Variable
                                                 └──Variable: r
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: a7303
                                              └──Desc: Variable
                                                 └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: pre_subst
                └──Abstraction:
                   └──Variables: a7371
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a7358
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a7371
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a7358
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a7371
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a7358
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a7371
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a7358
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a7371
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a7358
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a7371
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: a7358
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: a7358
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a7358
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a7358
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a7358
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a7358
                                                    └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a7371
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a7358
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a7371
                                                    └──Desc: Variable
                                                       └──Variable: f
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a7358
                                                    └──Desc: Variable
                                                       └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a7358
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Leaf
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a7358
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a7371
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Leaf
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a7371
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a7358
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fork
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7358
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7358
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a7358
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a7358
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a7358
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7358
                                                          └──Desc: Variable: t1
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7358
                                                          └──Desc: Variable: t2
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a7371
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fork
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7371
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7371
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a7371
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a7371
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a7371
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7371
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a7358
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a7371
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: a7358
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a7371
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a7358
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a7371
                                                                      └──Desc: Variable
                                                                         └──Variable: pre_subst
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: a7358
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: a7371
                                                                      └──Desc: Variable
                                                                         └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a7358
                                                                └──Desc: Variable
                                                                   └──Variable: t1
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7371
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a7358
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a7371
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: a7358
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a7371
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a7358
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a7371
                                                                      └──Desc: Variable
                                                                         └──Variable: pre_subst
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: a7358
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: a7371
                                                                      └──Desc: Variable
                                                                         └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a7358
                                                                └──Desc: Variable
                                                                   └──Variable: t2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: a7425
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a7427
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a7399
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a7425
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a7399
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a7427
                   └──Desc: Variable: comp_subst
                └──Abstraction:
                   └──Variables: a7399
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a7425
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a7427
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a7399
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a7425
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a7399
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a7427
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a7425
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a7427
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: a7399
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a7425
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: a7399
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a7427
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Variable: a7399
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: a7425
                                  └──Desc: Variable: g
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Variable: a7399
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: a7427
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: a7399
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: a7427
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a7425
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a7427
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a7425
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7427
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7425
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7427
                                                    └──Desc: Variable
                                                       └──Variable: pre_subst
                                                       └──Type expr: Variable: a7427
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a7425
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a7427
                                                    └──Desc: Variable
                                                       └──Variable: f
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a7425
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a7399
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a7425
                                                    └──Desc: Variable
                                                       └──Variable: g
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a7399
                                                    └──Desc: Variable
                                                       └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: thin
                └──Abstraction:
                   └──Variables: a7449
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a7481
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a7481
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a7481
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a7481
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a7481
                               └──Type expr: Constructor: fin
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: a7481
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: a7481
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: a7481
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Variable: a7481
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: a7481
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a7481
                                              └──Desc: Variable
                                                 └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: a7481
                                              └──Desc: Variable
                                                 └──Variable: y
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a7481
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: a7481
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a7481
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a7481
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a7481
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a7481
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a7481
                                                    └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a7481
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fin_succ
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a7481
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a7481
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a7481
                                                    └──Desc: Variable
                                                       └──Variable: y
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a7481
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a7481
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a7481
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a7553
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a7481
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a7553
                                                          └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a7481
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a7481
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a7481
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fin_zero
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: unit
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a7481
                                                 └──Expression:
                                                    └──Type expr: Constructor: unit
                                                    └──Desc: Constant: ()
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a7481
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a7481
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a7481
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a7593
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a7481
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a7593
                                                          └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a7481
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a7590
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a7481
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a7590
                                                          └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a7481
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fin_succ
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a7481
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a7481
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a7481
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a7590
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a7481
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: a7593
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: a7590
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: a7481
                                                                └──Desc: Variable
                                                                   └──Variable: thin
                                                                   └──Type expr: Variable: a7590
                                                             └──Expression:
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: a7593
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a7590
                                                          └──Desc: Variable
                                                             └──Variable: y
       └──Structure item: Type
          └──Type declaration:
             └──Type name: option
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: None
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: a
                └──Constructor declaration:
                   └──Constructor name: Some
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: a
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: a7662
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a7662
                            └──Type expr: Constructor: option
                               └──Type expr: Variable: a7656
                         └──Type expr: Constructor: option
                            └──Type expr: Variable: a7656
                   └──Desc: Variable: bind
                └──Abstraction:
                   └──Variables: a7662,a7662,a7662
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: option
                            └──Type expr: Variable: a7662
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: a7662
                               └──Type expr: Constructor: option
                                  └──Type expr: Variable: a7656
                            └──Type expr: Constructor: option
                               └──Type expr: Variable: a7656
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: option
                               └──Type expr: Variable: a7662
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a7662
                                  └──Type expr: Constructor: option
                                     └──Type expr: Variable: a7656
                               └──Type expr: Constructor: option
                                  └──Type expr: Variable: a7656
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a7662
                                     └──Type expr: Constructor: option
                                        └──Type expr: Variable: a7656
                                  └──Desc: Variable: f
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Variable: a7656
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: option
                                           └──Type expr: Variable: a7662
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Constructor: option
                                        └──Type expr: Variable: a7662
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Variable: a7662
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: None
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Variable: a7662
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Variable: a7656
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: None
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Variable: a7656
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Variable: a7662
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Some
                                                    └──Constructor argument type:
                                                       └──Type expr: Variable: a7662
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Variable: a7662
                                                 └──Pattern:
                                                    └──Type expr: Variable: a7662
                                                    └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Variable: a7656
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: a7662
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Variable: a7656
                                                    └──Desc: Variable
                                                       └──Variable: f
                                                 └──Expression:
                                                    └──Type expr: Variable: a7662
                                                    └──Desc: Variable
                                                       └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: thick
                └──Abstraction:
                   └──Variables: a7682
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a7716
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a7716
                            └──Type expr: Constructor: option
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a7716
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a7716
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: a7716
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: a7716
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: a7716
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Variable: a7716
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Variable: a7716
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Variable: a7716
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a7716
                                              └──Desc: Variable
                                                 └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a7716
                                              └──Desc: Variable
                                                 └──Variable: y
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a7716
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a7716
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a7716
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a7716
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a7716
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a7716
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a7716
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a7716
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a7716
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: None
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a7716
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a7716
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a7716
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a7716
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a7716
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a7716
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a7794
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a7716
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a7794
                                                          └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a7716
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Some
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a7716
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a7716
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a7716
                                                    └──Desc: Variable
                                                       └──Variable: y
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a7716
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a7716
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a7716
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a7832
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a7716
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a7832
                                                          └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a7716
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a7716
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a7716
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Constructor: is_succ
                                                       └──Type expr: Variable: a7832
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a7832
                                                             └──Type expr: Constructor: is_succ
                                                                └──Type expr: Variable: a7832
                                                          └──Desc: Variable
                                                             └──Variable: fin_succ
                                                             └──Type expr: Variable: a7832
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a7832
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Type expr: Constructor: is_succ
                                                    └──Type expr: Variable: a7832
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Constructor: is_succ
                                                             └──Type expr: Variable: a7832
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Is_succ
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: unit
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: is_succ
                                                                      └──Type expr: Variable: a7832
                                                             └──Pattern:
                                                                └──Type expr: Constructor: unit
                                                                └──Desc: Constant: ()
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a7716
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Some
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: a7716
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: a7716
                                                             └──Expression:
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: a7716
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Fin_zero
                                                                      └──Constructor argument type:
                                                                         └──Type expr: Constructor: unit
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: a7716
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: unit
                                                                      └──Desc: Constant: ()
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a7716
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a7716
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a7716
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a7910
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a7716
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a7910
                                                          └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a7716
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a7907
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a7716
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a7907
                                                          └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a7716
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Constructor: is_succ
                                                       └──Type expr: Variable: a7910
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a7910
                                                             └──Type expr: Constructor: is_succ
                                                                └──Type expr: Variable: a7910
                                                          └──Desc: Variable
                                                             └──Variable: fin_succ
                                                             └──Type expr: Variable: a7910
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a7910
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Type expr: Constructor: is_succ
                                                    └──Type expr: Variable: a7910
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Constructor: is_succ
                                                             └──Type expr: Variable: a7910
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Is_succ
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: unit
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: is_succ
                                                                      └──Type expr: Variable: a7910
                                                             └──Pattern:
                                                                └──Type expr: Constructor: unit
                                                                └──Desc: Constant: ()
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a7716
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: a8011
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: a7716
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: a7716
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: option
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: a8011
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Variable: a8011
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Variable: a7716
                                                                            └──Type expr: Constructor: option
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Variable: a7716
                                                                      └──Desc: Variable
                                                                         └──Variable: bind
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: a8011
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: a8011
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Variable: a7907
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Variable: a8011
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: fin
                                                                                        └──Type expr: Variable: a7910
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: fin
                                                                                           └──Type expr: Variable: a7907
                                                                                        └──Type expr: Constructor: option
                                                                                           └──Type expr: Constructor: fin
                                                                                              └──Type expr: Variable: a8011
                                                                                  └──Desc: Variable
                                                                                     └──Variable: thick
                                                                                     └──Type expr: Variable: a8011
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Variable: a7910
                                                                                  └──Desc: Variable
                                                                                     └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: a7907
                                                                            └──Desc: Variable
                                                                               └──Variable: y
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: a8011
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: a7716
                                                                └──Desc: Function
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: a8011
                                                                      └──Desc: Variable: x
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: a7716
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Some
                                                                            └──Constructor argument type:
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Variable: a7716
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Variable: a7716
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: a7716
                                                                            └──Desc: Construct
                                                                               └──Constructor description:
                                                                                  └──Name: Fin_succ
                                                                                  └──Constructor argument type:
                                                                                     └──Type expr: Constructor: fin
                                                                                        └──Type expr: Variable: a8011
                                                                                  └──Constructor type:
                                                                                     └──Type expr: Constructor: fin
                                                                                        └──Type expr: Variable: a7716
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Variable: a8011
                                                                                  └──Desc: Variable
                                                                                     └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: check
                └──Abstraction:
                   └──Variables: a8035
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a8069
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a8069
                            └──Type expr: Constructor: option
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a8069
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a8069
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: a8069
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a8069
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: a8069
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: a8069
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: term
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a8069
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Constructor: term
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: a8069
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a8069
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8069
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8069
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a8069
                                                    └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a8069
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a8069
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a8069
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8069
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: a8069
                                                             └──Type expr: Arrow
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: a8069
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a8069
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8069
                                                          └──Desc: Variable
                                                             └──Variable: bind
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a8069
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a8069
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Constructor: succ
                                                                         └──Type expr: Variable: a8069
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: a8069
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Constructor: succ
                                                                               └──Type expr: Variable: a8069
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Constructor: succ
                                                                                  └──Type expr: Variable: a8069
                                                                            └──Type expr: Constructor: option
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Variable: a8069
                                                                      └──Desc: Variable
                                                                         └──Variable: thick
                                                                         └──Type expr: Variable: a8069
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: a8069
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: a8069
                                                                └──Desc: Variable
                                                                   └──Variable: y
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a8069
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8069
                                                    └──Desc: Function
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a8069
                                                          └──Desc: Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a8069
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Some
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8069
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a8069
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a8069
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Var
                                                                      └──Constructor argument type:
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: a8069
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: a8069
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: a8069
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a8069
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Leaf
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8069
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a8069
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Some
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a8069
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8069
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a8069
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Leaf
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a8069
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a8069
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fork
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a8069
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a8069
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8069
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8069
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8069
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a8069
                                                          └──Desc: Variable: t1
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a8069
                                                          └──Desc: Variable: t2
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a8069
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8069
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a8069
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8069
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a8069
                                                             └──Type expr: Arrow
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8069
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a8069
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8069
                                                          └──Desc: Variable
                                                             └──Variable: bind
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a8069
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a8069
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Constructor: succ
                                                                         └──Type expr: Variable: a8069
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a8069
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Constructor: succ
                                                                               └──Type expr: Variable: a8069
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Constructor: succ
                                                                                  └──Type expr: Variable: a8069
                                                                            └──Type expr: Constructor: option
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Variable: a8069
                                                                      └──Desc: Variable
                                                                         └──Variable: check
                                                                         └──Type expr: Variable: a8069
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: a8069
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: a8069
                                                                └──Desc: Variable
                                                                   └──Variable: t1
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a8069
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8069
                                                    └──Desc: Function
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8069
                                                          └──Desc: Variable: t1
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a8069
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a8069
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: a8069
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a8069
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: option
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a8069
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Variable: a8069
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: term
                                                                                     └──Type expr: Variable: a8069
                                                                            └──Type expr: Constructor: option
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Variable: a8069
                                                                      └──Desc: Variable
                                                                         └──Variable: bind
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: a8069
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: a8069
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Constructor: succ
                                                                                     └──Type expr: Variable: a8069
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: term
                                                                                     └──Type expr: Variable: a8069
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: fin
                                                                                        └──Type expr: Constructor: succ
                                                                                           └──Type expr: Variable: a8069
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Constructor: succ
                                                                                              └──Type expr: Variable: a8069
                                                                                        └──Type expr: Constructor: option
                                                                                           └──Type expr: Constructor: term
                                                                                              └──Type expr: Variable: a8069
                                                                                  └──Desc: Variable
                                                                                     └──Variable: check
                                                                                     └──Type expr: Variable: a8069
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Constructor: succ
                                                                                        └──Type expr: Variable: a8069
                                                                                  └──Desc: Variable
                                                                                     └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Constructor: succ
                                                                                  └──Type expr: Variable: a8069
                                                                            └──Desc: Variable
                                                                               └──Variable: t2
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8069
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a8069
                                                                └──Desc: Function
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a8069
                                                                      └──Desc: Variable: t2
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: a8069
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Some
                                                                            └──Constructor argument type:
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Variable: a8069
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: term
                                                                                     └──Type expr: Variable: a8069
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a8069
                                                                            └──Desc: Construct
                                                                               └──Constructor description:
                                                                                  └──Name: Fork
                                                                                  └──Constructor argument type:
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Variable: a8069
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Variable: a8069
                                                                                  └──Constructor type:
                                                                                     └──Type expr: Constructor: term
                                                                                        └──Type expr: Variable: a8069
                                                                               └──Expression:
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Constructor: term
                                                                                        └──Type expr: Variable: a8069
                                                                                     └──Type expr: Constructor: term
                                                                                        └──Type expr: Variable: a8069
                                                                                  └──Desc: Tuple
                                                                                     └──Expression:
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Variable: a8069
                                                                                        └──Desc: Variable
                                                                                           └──Variable: t1
                                                                                     └──Expression:
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Variable: a8069
                                                                                        └──Desc: Variable
                                                                                           └──Variable: t2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: fin
                         └──Type expr: Constructor: succ
                            └──Type expr: Variable: a8324
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a8324
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a8324
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a8324
                   └──Desc: Variable: subst_var
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a8324
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a8324
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: a8324
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a8324
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a8324
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a8324
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: a8324
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a8324
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a8324
                                  └──Desc: Variable: t'
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: a8324
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: a8324
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a8324
                                        └──Desc: Variable: y
                                     └──Expression:
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: a8324
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a8324
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8324
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a8324
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a8324
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: a8324
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: a8324
                                                          └──Desc: Variable
                                                             └──Variable: thick
                                                             └──Type expr: Variable: a8324
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a8324
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a8324
                                                    └──Desc: Variable
                                                       └──Variable: y
                                           └──Type expr: Constructor: option
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: a8324
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a8324
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: None
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: a8324
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a8324
                                                    └──Desc: Variable
                                                       └──Variable: t'
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a8324
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Some
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a8324
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: a8324
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a8324
                                                          └──Desc: Variable: y'
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a8324
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Var
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a8324
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a8324
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a8324
                                                          └──Desc: Variable
                                                             └──Variable: y'
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: fin
                         └──Type expr: Constructor: succ
                            └──Type expr: Variable: a8346
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a8346
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a8346
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a8346
                   └──Desc: Variable: subst
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a8346
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a8346
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: a8346
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a8346
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a8346
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a8346
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: term
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: a8346
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a8346
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a8346
                                  └──Desc: Variable: t'
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: term
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: a8346
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: a8346
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a8346
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a8346
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a8346
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a8346
                                        └──Desc: Variable
                                           └──Variable: pre_subst
                                           └──Type expr: Variable: a8346
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Variable: a8346
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: a8346
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a8346
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a8346
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a8346
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8346
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8346
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a8346
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a8346
                                                    └──Desc: Variable
                                                       └──Variable: subst_var
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a8346
                                                    └──Desc: Variable
                                                       └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a8346
                                              └──Desc: Variable
                                                 └──Variable: t'
       └──Structure item: Type
          └──Type declaration:
             └──Type name: alist
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Anil
                   └──Constructor alphas: m n
                   └──Constructor type:
                      └──Type expr: Constructor: alist
                         └──Type expr: Variable: m
                         └──Type expr: Variable: n
                   └──Constraint:
                      └──Type expr: Variable: m
                      └──Type expr: Variable: n
                └──Constructor declaration:
                   └──Constructor name: Asnoc
                   └──Constructor alphas: m n
                   └──Constructor type:
                      └──Type expr: Constructor: alist
                         └──Type expr: Variable: m
                         └──Type expr: Variable: n
                   └──Constructor argument:
                      └──Constructor betas: m1
                      └──Type expr: Tuple
                         └──Type expr: Constructor: alist
                            └──Type expr: Variable: m1
                            └──Type expr: Variable: n
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: m1
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: m1
                   └──Constraint:
                      └──Type expr: Variable: m
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: m1
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: sub
                └──Abstraction:
                   └──Variables: a8376,a8375
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: alist
                            └──Type expr: Variable: a8403
                            └──Type expr: Variable: a8404
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a8403
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a8404
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: a8403
                               └──Type expr: Variable: a8404
                            └──Desc: Variable: s
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a8403
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a8404
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: alist
                                     └──Type expr: Variable: a8403
                                     └──Type expr: Variable: a8404
                                  └──Desc: Variable
                                     └──Variable: s
                               └──Type expr: Constructor: alist
                                  └──Type expr: Variable: a8403
                                  └──Type expr: Variable: a8404
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Variable: a8403
                                           └──Type expr: Variable: a8404
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Anil
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: a8403
                                                    └──Type expr: Variable: a8404
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: a8403
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: a8404
                                        └──Desc: Variable
                                           └──Variable: var
                                           └──Type expr: Variable: a8403
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Variable: a8403
                                           └──Type expr: Variable: a8404
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Asnoc
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: a8469
                                                       └──Type expr: Variable: a8404
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a8469
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a8469
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: a8403
                                                    └──Type expr: Variable: a8404
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: a8469
                                                    └──Type expr: Variable: a8404
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a8469
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a8469
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: a8469
                                                       └──Type expr: Variable: a8404
                                                    └──Desc: Variable: s
                                                 └──Pattern:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a8469
                                                    └──Desc: Variable: t
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a8469
                                                    └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: a8403
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: a8404
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a8403
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a8469
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a8403
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a8404
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a8469
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8404
                                                       └──Type expr: Arrow
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a8403
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a8469
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a8403
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a8404
                                                    └──Desc: Variable
                                                       └──Variable: comp_subst
                                                       └──Type expr: Variable: a8403
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a8469
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a8404
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: alist
                                                                └──Type expr: Variable: a8469
                                                                └──Type expr: Variable: a8404
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: a8469
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a8404
                                                          └──Desc: Variable
                                                             └──Variable: sub
                                                             └──Type expr: Variable: a8404
                                                             └──Type expr: Variable: a8469
                                                       └──Expression:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: a8469
                                                             └──Type expr: Variable: a8404
                                                          └──Desc: Variable
                                                             └──Variable: s
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a8403
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a8469
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a8469
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a8403
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8469
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a8469
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a8469
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: a8403
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8469
                                                          └──Desc: Variable
                                                             └──Variable: subst_var
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a8469
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a8469
                                                    └──Desc: Variable
                                                       └──Variable: t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: append
                └──Abstraction:
                   └──Variables: a8557,a8561,a8560
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: alist
                            └──Type expr: Variable: a8591
                            └──Type expr: Variable: a8592
                         └──Type expr: Arrow
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: a8603
                               └──Type expr: Variable: a8591
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: a8603
                               └──Type expr: Variable: a8592
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: a8591
                               └──Type expr: Variable: a8592
                            └──Desc: Variable: s1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: alist
                                  └──Type expr: Variable: a8603
                                  └──Type expr: Variable: a8591
                               └──Type expr: Constructor: alist
                                  └──Type expr: Variable: a8603
                                  └──Type expr: Variable: a8592
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: alist
                                     └──Type expr: Variable: a8603
                                     └──Type expr: Variable: a8591
                                  └──Desc: Variable: s2
                               └──Expression:
                                  └──Type expr: Constructor: alist
                                     └──Type expr: Variable: a8603
                                     └──Type expr: Variable: a8592
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Variable: a8603
                                           └──Type expr: Variable: a8591
                                        └──Desc: Variable
                                           └──Variable: s2
                                     └──Type expr: Constructor: alist
                                        └──Type expr: Variable: a8603
                                        └──Type expr: Variable: a8591
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: a8603
                                                 └──Type expr: Variable: a8591
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Anil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: a8603
                                                          └──Type expr: Variable: a8591
                                           └──Expression:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: a8603
                                                 └──Type expr: Variable: a8592
                                              └──Desc: Variable
                                                 └──Variable: s1
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: a8603
                                                 └──Type expr: Variable: a8591
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Asnoc
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: a8652
                                                             └──Type expr: Variable: a8591
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8652
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a8652
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: a8603
                                                          └──Type expr: Variable: a8591
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: a8652
                                                          └──Type expr: Variable: a8591
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a8652
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8652
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: a8652
                                                             └──Type expr: Variable: a8591
                                                          └──Desc: Variable: s2
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8652
                                                          └──Desc: Variable: t
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a8652
                                                          └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: a8603
                                                 └──Type expr: Variable: a8592
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Asnoc
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: a8652
                                                             └──Type expr: Variable: a8592
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8652
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a8652
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: a8603
                                                          └──Type expr: Variable: a8592
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: a8652
                                                          └──Type expr: Variable: a8592
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a8652
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8652
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: a8652
                                                             └──Type expr: Variable: a8592
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: alist
                                                                      └──Type expr: Variable: a8652
                                                                      └──Type expr: Variable: a8591
                                                                   └──Type expr: Constructor: alist
                                                                      └──Type expr: Variable: a8652
                                                                      └──Type expr: Variable: a8592
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: alist
                                                                            └──Type expr: Variable: a8591
                                                                            └──Type expr: Variable: a8592
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: alist
                                                                               └──Type expr: Variable: a8652
                                                                               └──Type expr: Variable: a8591
                                                                            └──Type expr: Constructor: alist
                                                                               └──Type expr: Variable: a8652
                                                                               └──Type expr: Variable: a8592
                                                                      └──Desc: Variable
                                                                         └──Variable: append
                                                                         └──Type expr: Variable: a8652
                                                                         └──Type expr: Variable: a8592
                                                                         └──Type expr: Variable: a8591
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: alist
                                                                         └──Type expr: Variable: a8591
                                                                         └──Type expr: Variable: a8592
                                                                      └──Desc: Variable
                                                                         └──Variable: s1
                                                             └──Expression:
                                                                └──Type expr: Constructor: alist
                                                                   └──Type expr: Variable: a8652
                                                                   └──Type expr: Variable: a8591
                                                                └──Desc: Variable
                                                                   └──Variable: s2
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8652
                                                          └──Desc: Variable
                                                             └──Variable: t
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a8652
                                                          └──Desc: Variable
                                                             └──Variable: x
       └──Structure item: Type
          └──Type declaration:
             └──Type name: ex_alist
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Exists_alist
                   └──Constructor alphas: m
                   └──Constructor type:
                      └──Type expr: Constructor: ex_alist
                         └──Type expr: Variable: m
                   └──Constructor argument:
                      └──Constructor betas: n
                      └──Type expr: Constructor: alist
                         └──Type expr: Variable: m
                         └──Type expr: Variable: n
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: alist
                         └──Type expr: Variable: a8739
                         └──Type expr: Variable: a8738
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a8739
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a8739
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a8739
                   └──Desc: Variable: asnoc
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: alist
                            └──Type expr: Variable: a8739
                            └──Type expr: Variable: a8738
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a8739
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: a8739
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: a8739
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: a8739
                               └──Type expr: Variable: a8738
                            └──Desc: Variable: a
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a8739
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: a8739
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: a8739
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a8739
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: a8739
                                     └──Type expr: Constructor: ex_alist
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: a8739
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a8739
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a8739
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Exists_alist
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a8739
                                                    └──Type expr: Variable: a8738
                                              └──Constructor type:
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a8739
                                           └──Expression:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a8739
                                                 └──Type expr: Variable: a8738
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Asnoc
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: a8739
                                                             └──Type expr: Variable: a8738
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8739
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a8739
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8739
                                                          └──Type expr: Variable: a8738
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: a8739
                                                          └──Type expr: Variable: a8738
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a8739
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8739
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: a8739
                                                             └──Type expr: Variable: a8738
                                                          └──Desc: Variable
                                                             └──Variable: a
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8739
                                                          └──Desc: Variable
                                                             └──Variable: t
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a8739
                                                          └──Desc: Variable
                                                             └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: weaken_fin
                └──Abstraction:
                   └──Variables: a8767
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: a8788
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a8788
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a8788
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a8788
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: a8788
                                  └──Desc: Variable
                                     └──Variable: f
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a8788
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: a8788
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_zero
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a8788
                                           └──Pattern:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
                                     └──Expression:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a8788
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_zero
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a8788
                                           └──Expression:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: a8788
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a8834
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a8788
                                           └──Pattern:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: a8834
                                              └──Desc: Variable: f
                                     └──Expression:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a8788
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a8788
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a8788
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: a8788
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a8834
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a8788
                                                    └──Desc: Variable
                                                       └──Variable: weaken_fin
                                                       └──Type expr: Variable: a8834
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a8834
                                                    └──Desc: Variable
                                                       └──Variable: f
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: term
                         └──Type expr: Variable: a8903
                      └──Type expr: Constructor: term
                         └──Type expr: Constructor: succ
                            └──Type expr: Variable: a8903
                   └──Desc: Variable: weaken_term
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a8903
                         └──Type expr: Constructor: term
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a8903
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a8903
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: term
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a8903
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: a8903
                                     └──Type expr: Constructor: term
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: a8903
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: a8903
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a8903
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a8903
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a8903
                                        └──Desc: Variable
                                           └──Variable: pre_subst
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a8903
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: a8903
                                           └──Type expr: Constructor: term
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Variable: a8903
                                        └──Desc: Function
                                           └──Pattern:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: a8903
                                              └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a8903
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8903
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8903
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a8903
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a8903
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a8903
                                                          └──Desc: Variable
                                                             └──Variable: weaken_fin
                                                             └──Type expr: Variable: a8903
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a8903
                                                          └──Desc: Variable
                                                             └──Variable: x
                               └──Expression:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a8903
                                  └──Desc: Variable
                                     └──Variable: t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: weaken_alist
                └──Abstraction:
                   └──Variables: a8918,a8917
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: alist
                            └──Type expr: Variable: a8945
                            └──Type expr: Variable: a8946
                         └──Type expr: Constructor: alist
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a8945
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a8946
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: a8945
                               └──Type expr: Variable: a8946
                            └──Desc: Variable: s
                         └──Expression:
                            └──Type expr: Constructor: alist
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a8945
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a8946
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: alist
                                     └──Type expr: Variable: a8945
                                     └──Type expr: Variable: a8946
                                  └──Desc: Variable
                                     └──Variable: s
                               └──Type expr: Constructor: alist
                                  └──Type expr: Variable: a8945
                                  └──Type expr: Variable: a8946
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Variable: a8945
                                           └──Type expr: Variable: a8946
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Anil
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: a8945
                                                    └──Type expr: Variable: a8946
                                     └──Expression:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a8945
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a8946
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Anil
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a8945
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a8945
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Variable: a8945
                                           └──Type expr: Variable: a8946
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Asnoc
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: a9011
                                                       └──Type expr: Variable: a8946
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a9011
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a9011
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: a8945
                                                    └──Type expr: Variable: a8946
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: a9011
                                                    └──Type expr: Variable: a8946
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a9011
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a9011
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: a9011
                                                       └──Type expr: Variable: a8946
                                                    └──Desc: Variable: s
                                                 └──Pattern:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a9011
                                                    └──Desc: Variable: t
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a9011
                                                    └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a8945
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a8946
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Asnoc
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: a8945
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a8946
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a8945
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a8945
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a8945
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a8946
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: a8945
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a8946
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a8945
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a8945
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: a8945
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a8946
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: alist
                                                                └──Type expr: Variable: a9011
                                                                └──Type expr: Variable: a8946
                                                             └──Type expr: Constructor: alist
                                                                └──Type expr: Variable: a8945
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a8946
                                                          └──Desc: Variable
                                                             └──Variable: weaken_alist
                                                             └──Type expr: Variable: a8946
                                                             └──Type expr: Variable: a9011
                                                       └──Expression:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: a9011
                                                             └──Type expr: Variable: a8946
                                                          └──Desc: Variable
                                                             └──Variable: s
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a8945
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a9011
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a8945
                                                          └──Desc: Variable
                                                             └──Variable: weaken_term
                                                             └──Type expr: Variable: a9011
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a9011
                                                          └──Desc: Variable
                                                             └──Variable: t
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a8945
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a8945
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a8945
                                                          └──Desc: Variable
                                                             └──Variable: weaken_fin
                                                             └──Type expr: Variable: a8945
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a8945
                                                          └──Desc: Variable
                                                             └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: sub'
                └──Abstraction:
                   └──Variables: a9110
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ex_alist
                            └──Type expr: Variable: a9134
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a9134
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a9134
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Variable: a9134
                            └──Desc: Variable: e
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a9134
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a9134
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Variable: a9134
                                  └──Desc: Variable
                                     └──Variable: e
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Variable: a9134
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: a9134
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Exists_alist
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: a9134
                                                    └──Type expr: Variable: a9159
                                              └──Constructor type:
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Variable: a9134
                                           └──Pattern:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: a9134
                                                 └──Type expr: Variable: a9159
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Anil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: a9134
                                                          └──Type expr: Variable: a9159
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: a9134
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: a9134
                                        └──Desc: Variable
                                           └──Variable: var
                                           └──Type expr: Variable: a9134
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: a9134
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Exists_alist
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: a9134
                                                    └──Type expr: Variable: a9190
                                              └──Constructor type:
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Variable: a9134
                                           └──Pattern:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: a9134
                                                 └──Type expr: Variable: a9190
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Asnoc
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: a9209
                                                             └──Type expr: Variable: a9190
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a9209
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a9209
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: a9134
                                                          └──Type expr: Variable: a9190
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: a9209
                                                          └──Type expr: Variable: a9190
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a9209
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a9209
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: a9209
                                                             └──Type expr: Variable: a9190
                                                          └──Desc: Variable: s
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a9209
                                                          └──Desc: Variable: t
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a9209
                                                          └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: a9134
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: a9134
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a9134
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a9134
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a9134
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a9134
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a9134
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a9134
                                                       └──Type expr: Arrow
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a9134
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a9134
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a9134
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a9134
                                                    └──Desc: Variable
                                                       └──Variable: comp_subst
                                                       └──Type expr: Variable: a9134
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a9134
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a9134
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: ex_alist
                                                                └──Type expr: Variable: a9134
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: a9134
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a9134
                                                          └──Desc: Variable
                                                             └──Variable: sub'
                                                             └──Type expr: Variable: a9134
                                                       └──Expression:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: a9134
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Exists_alist
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: alist
                                                                      └──Type expr: Variable: a9134
                                                                      └──Type expr: Constructor: succ
                                                                         └──Type expr: Variable: a9190
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: ex_alist
                                                                      └──Type expr: Variable: a9134
                                                             └──Expression:
                                                                └──Type expr: Constructor: alist
                                                                   └──Type expr: Variable: a9134
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: a9190
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: alist
                                                                            └──Type expr: Variable: a9209
                                                                            └──Type expr: Variable: a9190
                                                                         └──Type expr: Constructor: alist
                                                                            └──Type expr: Variable: a9134
                                                                            └──Type expr: Constructor: succ
                                                                               └──Type expr: Variable: a9190
                                                                      └──Desc: Variable
                                                                         └──Variable: weaken_alist
                                                                         └──Type expr: Variable: a9190
                                                                         └──Type expr: Variable: a9209
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: alist
                                                                         └──Type expr: Variable: a9209
                                                                         └──Type expr: Variable: a9190
                                                                      └──Desc: Variable
                                                                         └──Variable: s
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a9134
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a9134
                                              └──Desc: Function
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a9134
                                                    └──Desc: Variable: t'
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a9134
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a9209
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a9134
                                                          └──Desc: Variable
                                                             └──Variable: weaken_term
                                                             └──Type expr: Variable: a9209
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a9209
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: a9134
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a9209
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: a9209
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: a9134
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a9209
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Constructor: succ
                                                                                     └──Type expr: Variable: a9209
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: term
                                                                                     └──Type expr: Variable: a9209
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: fin
                                                                                        └──Type expr: Variable: a9134
                                                                                     └──Type expr: Constructor: term
                                                                                        └──Type expr: Variable: a9209
                                                                            └──Desc: Variable
                                                                               └──Variable: subst_var
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Constructor: succ
                                                                                  └──Type expr: Variable: a9209
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a9209
                                                                      └──Desc: Variable
                                                                         └──Variable: t
                                                             └──Expression:
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: a9134
                                                                └──Desc: Variable
                                                                   └──Variable: t'
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: ex_alist
                         └──Type expr: Variable: a9337
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a9337
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a9337
                   └──Desc: Variable: subst'
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ex_alist
                            └──Type expr: Variable: a9337
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a9337
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a9337
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Variable: a9337
                            └──Desc: Variable: e
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a9337
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a9337
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Arrow
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: a9337
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: a9337
                                     └──Type expr: Arrow
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: a9337
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: a9337
                                  └──Desc: Variable
                                     └──Variable: pre_subst
                                     └──Type expr: Variable: a9337
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Variable: a9337
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: a9337
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: ex_alist
                                              └──Type expr: Variable: a9337
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: a9337
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a9337
                                        └──Desc: Variable
                                           └──Variable: sub'
                                           └──Type expr: Variable: a9337
                                     └──Expression:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: a9337
                                        └──Desc: Variable
                                           └──Variable: e
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: fin
                         └──Type expr: Constructor: succ
                            └──Type expr: Variable: a9401
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a9401
                         └──Type expr: Constructor: ex_alist
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a9401
                   └──Desc: Variable: flex_flex
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a9401
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a9401
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a9401
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a9401
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: a9401
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: a9401
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: a9401
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: a9401
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: option
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: a9401
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a9401
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a9401
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a9401
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a9401
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a9401
                                                    └──Desc: Variable
                                                       └──Variable: thick
                                                       └──Type expr: Variable: a9401
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a9401
                                                    └──Desc: Variable
                                                       └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a9401
                                              └──Desc: Variable
                                                 └──Variable: y
                                     └──Type expr: Constructor: option
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: a9401
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a9401
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Some
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a9401
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a9401
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a9401
                                                    └──Desc: Variable: y'
                                           └──Expression:
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a9401
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a9401
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a9401
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a9401
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: a9401
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: a9401
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: alist
                                                                      └──Type expr: Variable: a9401
                                                                      └──Type expr: Variable: a9401
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a9401
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Constructor: succ
                                                                               └──Type expr: Variable: a9401
                                                                         └──Type expr: Constructor: ex_alist
                                                                            └──Type expr: Constructor: succ
                                                                               └──Type expr: Variable: a9401
                                                                └──Desc: Variable
                                                                   └──Variable: asnoc
                                                                   └──Type expr: Variable: a9401
                                                                   └──Type expr: Variable: a9401
                                                             └──Expression:
                                                                └──Type expr: Constructor: alist
                                                                   └──Type expr: Variable: a9401
                                                                   └──Type expr: Variable: a9401
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Anil
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: alist
                                                                            └──Type expr: Variable: a9401
                                                                            └──Type expr: Variable: a9401
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a9401
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Var
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: a9401
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a9401
                                                             └──Expression:
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: a9401
                                                                └──Desc: Variable
                                                                   └──Variable: y'
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a9401
                                                    └──Desc: Variable
                                                       └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a9401
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: None
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a9401
                                           └──Expression:
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a9401
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Exists_alist
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a9401
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a9401
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a9401
                                                 └──Expression:
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a9401
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a9401
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Anil
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: alist
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a9401
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a9401
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: fin
                         └──Type expr: Constructor: succ
                            └──Type expr: Variable: a9483
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a9483
                         └──Type expr: Constructor: option
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a9483
                   └──Desc: Variable: flex_rigid
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a9483
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a9483
                            └──Type expr: Constructor: option
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: a9483
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a9483
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: a9483
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: a9483
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: a9483
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Constructor: ex_alist
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: a9483
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a9483
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a9483
                                           └──Type expr: Constructor: option
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a9483
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a9483
                                                 └──Type expr: Arrow
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a9483
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a9483
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a9483
                                              └──Desc: Variable
                                                 └──Variable: bind
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a9483
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a9483
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a9483
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a9483
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a9483
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: a9483
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a9483
                                                          └──Desc: Variable
                                                             └──Variable: check
                                                             └──Type expr: Variable: a9483
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a9483
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a9483
                                                    └──Desc: Variable
                                                       └──Variable: t
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: a9483
                                           └──Type expr: Constructor: option
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a9483
                                        └──Desc: Function
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a9483
                                              └──Desc: Variable: t'
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a9483
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Some
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a9483
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a9483
                                                 └──Expression:
                                                    └──Type expr: Constructor: ex_alist
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a9483
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a9483
                                                             └──Type expr: Constructor: ex_alist
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a9483
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a9483
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: a9483
                                                                      └──Type expr: Constructor: ex_alist
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: a9483
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: alist
                                                                            └──Type expr: Variable: a9483
                                                                            └──Type expr: Variable: a9483
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a9483
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Constructor: succ
                                                                                     └──Type expr: Variable: a9483
                                                                               └──Type expr: Constructor: ex_alist
                                                                                  └──Type expr: Constructor: succ
                                                                                     └──Type expr: Variable: a9483
                                                                      └──Desc: Variable
                                                                         └──Variable: asnoc
                                                                         └──Type expr: Variable: a9483
                                                                         └──Type expr: Variable: a9483
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: alist
                                                                         └──Type expr: Variable: a9483
                                                                         └──Type expr: Variable: a9483
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Anil
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: alist
                                                                                  └──Type expr: Variable: a9483
                                                                                  └──Type expr: Variable: a9483
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a9483
                                                                └──Desc: Variable
                                                                   └──Variable: t'
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a9483
                                                          └──Desc: Variable
                                                             └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: amgu
                └──Abstraction:
                   └──Variables: a9505
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a9536
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a9536
                            └──Type expr: Arrow
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Variable: a9536
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Variable: a9536
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a9536
                            └──Desc: Variable: s
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a9536
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Variable: a9536
                                  └──Type expr: Constructor: option
                                     └──Type expr: Constructor: ex_alist
                                        └──Type expr: Variable: a9536
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a9536
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: ex_alist
                                        └──Type expr: Variable: a9536
                                     └──Type expr: Constructor: option
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: a9536
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: a9536
                                        └──Desc: Variable: acc
                                     └──Expression:
                                        └──Type expr: Constructor: option
                                           └──Type expr: Constructor: ex_alist
                                              └──Type expr: Variable: a9536
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a9536
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a9536
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Variable: a9536
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a9536
                                                    └──Desc: Variable
                                                       └──Variable: s
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a9536
                                                    └──Desc: Variable
                                                       └──Variable: t
                                                 └──Expression:
                                                    └──Type expr: Constructor: ex_alist
                                                       └──Type expr: Variable: a9536
                                                    └──Desc: Variable
                                                       └──Variable: acc
                                           └──Type expr: Tuple
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a9536
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a9536
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Variable: a9536
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a9536
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a9536
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: a9536
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a9536
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Leaf
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a9536
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a9536
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Leaf
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a9536
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: a9536
                                                          └──Desc: Any
                                                 └──Expression:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: a9536
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Some
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: ex_alist
                                                                └──Type expr: Variable: a9536
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: a9536
                                                       └──Expression:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: a9536
                                                          └──Desc: Variable
                                                             └──Variable: acc
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a9536
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a9536
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: a9536
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a9536
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Leaf
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a9536
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a9536
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Fork
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a9536
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a9536
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a9536
                                                             └──Pattern:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a9536
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a9536
                                                                └──Desc: Any
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: a9536
                                                          └──Desc: Any
                                                 └──Expression:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: a9536
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: None
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: a9536
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a9536
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a9536
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: a9536
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a9536
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Fork
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a9536
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a9536
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a9536
                                                             └──Pattern:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a9536
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a9536
                                                                └──Desc: Any
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a9536
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Leaf
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a9536
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: a9536
                                                          └──Desc: Any
                                                 └──Expression:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: a9536
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: None
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: a9536
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a9536
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a9536
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: a9536
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a9536
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Fork
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a9536
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a9536
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a9536
                                                             └──Pattern:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a9536
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a9536
                                                                └──Desc: Tuple
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a9536
                                                                      └──Desc: Variable: s1
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a9536
                                                                      └──Desc: Variable: s2
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a9536
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Fork
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a9536
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a9536
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a9536
                                                             └──Pattern:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a9536
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a9536
                                                                └──Desc: Tuple
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a9536
                                                                      └──Desc: Variable: t1
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a9536
                                                                      └──Desc: Variable: t2
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: a9536
                                                          └──Desc: Any
                                                 └──Expression:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: a9536
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: a9536
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: ex_alist
                                                                      └──Type expr: Variable: a9536
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: a9536
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: ex_alist
                                                                         └──Type expr: Variable: a9536
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ex_alist
                                                                            └──Type expr: Variable: a9536
                                                                         └──Type expr: Constructor: option
                                                                            └──Type expr: Constructor: ex_alist
                                                                               └──Type expr: Variable: a9536
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: ex_alist
                                                                            └──Type expr: Variable: a9536
                                                                └──Desc: Variable
                                                                   └──Variable: bind
                                                                   └──Type expr: Constructor: ex_alist
                                                                      └──Type expr: Variable: a9536
                                                             └──Expression:
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: ex_alist
                                                                      └──Type expr: Variable: a9536
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ex_alist
                                                                            └──Type expr: Variable: a9536
                                                                         └──Type expr: Constructor: option
                                                                            └──Type expr: Constructor: ex_alist
                                                                               └──Type expr: Variable: a9536
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Variable: a9536
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: ex_alist
                                                                                     └──Type expr: Variable: a9536
                                                                                  └──Type expr: Constructor: option
                                                                                     └──Type expr: Constructor: ex_alist
                                                                                        └──Type expr: Variable: a9536
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: term
                                                                                        └──Type expr: Variable: a9536
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Variable: a9536
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Constructor: ex_alist
                                                                                              └──Type expr: Variable: a9536
                                                                                           └──Type expr: Constructor: option
                                                                                              └──Type expr: Constructor: ex_alist
                                                                                                 └──Type expr: Variable: a9536
                                                                                  └──Desc: Variable
                                                                                     └──Variable: amgu
                                                                                     └──Type expr: Variable: a9536
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: term
                                                                                     └──Type expr: Variable: a9536
                                                                                  └──Desc: Variable
                                                                                     └──Variable: s1
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a9536
                                                                            └──Desc: Variable
                                                                               └──Variable: t1
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ex_alist
                                                                         └──Type expr: Variable: a9536
                                                                      └──Desc: Variable
                                                                         └──Variable: acc
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: ex_alist
                                                                └──Type expr: Variable: a9536
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: a9536
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a9536
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: ex_alist
                                                                         └──Type expr: Variable: a9536
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: ex_alist
                                                                            └──Type expr: Variable: a9536
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: a9536
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a9536
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: ex_alist
                                                                                  └──Type expr: Variable: a9536
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: ex_alist
                                                                                     └──Type expr: Variable: a9536
                                                                      └──Desc: Variable
                                                                         └──Variable: amgu
                                                                         └──Type expr: Variable: a9536
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a9536
                                                                      └──Desc: Variable
                                                                         └──Variable: s2
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a9536
                                                                └──Desc: Variable
                                                                   └──Variable: t2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: term
                         └──Type expr: Variable: a9793
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a9793
                         └──Type expr: Constructor: option
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Variable: a9793
                   └──Desc: Variable: mgu
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a9793
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a9793
                            └──Type expr: Constructor: option
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Variable: a9793
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a9793
                            └──Desc: Variable: s
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a9793
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Variable: a9793
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a9793
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Constructor: ex_alist
                                        └──Type expr: Variable: a9793
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: ex_alist
                                              └──Type expr: Variable: a9793
                                           └──Type expr: Constructor: option
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Variable: a9793
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a9793
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: ex_alist
                                                       └──Type expr: Variable: a9793
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: a9793
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a9793
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a9793
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: ex_alist
                                                                └──Type expr: Variable: a9793
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: a9793
                                                    └──Desc: Variable
                                                       └──Variable: amgu
                                                       └──Type expr: Variable: a9793
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a9793
                                                    └──Desc: Variable
                                                       └──Variable: s
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a9793
                                              └──Desc: Variable
                                                 └──Variable: t
                                     └──Expression:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: a9793
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Exists_alist
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: a9793
                                                    └──Type expr: Variable: a9793
                                              └──Constructor type:
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Variable: a9793
                                           └──Expression:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: a9793
                                                 └──Type expr: Variable: a9793
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Anil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: a9793
                                                          └──Type expr: Variable: a9793 |}]

