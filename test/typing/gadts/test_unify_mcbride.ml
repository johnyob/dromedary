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
  [%expect
    {|
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
                   └──Constructor alphas: 366
                   └──Constructor type:
                      └──Type expr: Constructor: nat
                         └──Type expr: Variable: 366
                   └──Constraint:
                      └──Type expr: Variable: 366
                      └──Type expr: Constructor: zero
                └──Constructor declaration:
                   └──Constructor name: Succ
                   └──Constructor alphas: 366
                   └──Constructor type:
                      └──Type expr: Constructor: nat
                         └──Type expr: Variable: 366
                   └──Constructor argument:
                      └──Constructor betas: 369
                      └──Type expr: Constructor: nat
                         └──Type expr: Variable: 369
                   └──Constraint:
                      └──Type expr: Variable: 366
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: 369
       └──Structure item: Type
          └──Type declaration:
             └──Type name: fin
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Fin_zero
                   └──Constructor alphas: 373
                   └──Constructor type:
                      └──Type expr: Constructor: fin
                         └──Type expr: Variable: 373
                   └──Constructor argument:
                      └──Constructor betas: 374
                      └──Type expr: Constructor: unit
                   └──Constraint:
                      └──Type expr: Variable: 373
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: 374
                └──Constructor declaration:
                   └──Constructor name: Fin_succ
                   └──Constructor alphas: 373
                   └──Constructor type:
                      └──Type expr: Constructor: fin
                         └──Type expr: Variable: 373
                   └──Constructor argument:
                      └──Constructor betas: 378
                      └──Type expr: Constructor: fin
                         └──Type expr: Variable: 378
                   └──Constraint:
                      └──Type expr: Variable: 373
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: 378
       └──Structure item: Type
          └──Type declaration:
             └──Type name: is_succ
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Is_succ
                   └──Constructor alphas: 382
                   └──Constructor type:
                      └──Type expr: Constructor: is_succ
                         └──Type expr: Variable: 382
                   └──Constructor argument:
                      └──Constructor betas: 383
                      └──Type expr: Constructor: unit
                   └──Constraint:
                      └──Type expr: Variable: 382
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: 383
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: fin
                         └──Type expr: Variable: 9
                      └──Type expr: Constructor: is_succ
                         └──Type expr: Variable: 9
                   └──Desc: Variable: fin_succ
                └──Abstraction:
                   └──Variables: 9
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: 9
                         └──Type expr: Constructor: is_succ
                            └──Type expr: Variable: 9
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 9
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Constructor: is_succ
                               └──Type expr: Variable: 9
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: 9
                                  └──Desc: Variable
                                     └──Variable: f
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 9
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: 9
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_zero
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 9
                                           └──Pattern:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
                                     └──Expression:
                                        └──Type expr: Constructor: is_succ
                                           └──Type expr: Variable: 9
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Is_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: is_succ
                                                    └──Type expr: Variable: 9
                                           └──Expression:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: 9
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 50
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 9
                                           └──Pattern:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: 50
                                              └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Constructor: is_succ
                                           └──Type expr: Variable: 9
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Is_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: is_succ
                                                    └──Type expr: Variable: 9
                                           └──Expression:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
       └──Structure item: Type
          └──Type declaration:
             └──Type name: term
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Var
                   └──Constructor alphas: 387
                   └──Constructor type:
                      └──Type expr: Constructor: term
                         └──Type expr: Variable: 387
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: fin
                         └──Type expr: Variable: 387
                └──Constructor declaration:
                   └──Constructor name: Leaf
                   └──Constructor alphas: 387
                   └──Constructor type:
                      └──Type expr: Constructor: term
                         └──Type expr: Variable: 387
                └──Constructor declaration:
                   └──Constructor name: Fork
                   └──Constructor alphas: 387
                   └──Constructor type:
                      └──Type expr: Constructor: term
                         └──Type expr: Variable: 387
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 387
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 387
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: fin
                         └──Type expr: Variable: 79
                      └──Type expr: Constructor: term
                         └──Type expr: Variable: 79
                   └──Desc: Variable: var
                └──Abstraction:
                   └──Variables: 79
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: 79
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 79
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 79
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 79
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Var
                                  └──Constructor argument type:
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Variable: 79
                                  └──Constructor type:
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: 79
                               └──Expression:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: 79
                                  └──Desc: Variable
                                     └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: 85
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: 107
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: 85
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 107
                   └──Desc: Variable: lift
                └──Abstraction:
                   └──Variables: 107,107,85
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 85
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 107
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 85
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 107
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 85
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 107
                            └──Desc: Variable: r
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 85
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 107
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: 85
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 107
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Var
                                        └──Constructor argument type:
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: 107
                                        └──Constructor type:
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: 107
                                     └──Expression:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: 107
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 85
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 107
                                              └──Desc: Variable
                                                 └──Variable: r
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: 85
                                              └──Desc: Variable
                                                 └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: pre_subst
                └──Abstraction:
                   └──Variables: 153
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 140
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 153
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 140
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 153
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 140
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 153
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 140
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 153
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 140
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 153
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: 140
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: 140
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 140
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 140
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 140
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 140
                                                    └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 153
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 140
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 153
                                                    └──Desc: Variable
                                                       └──Variable: f
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 140
                                                    └──Desc: Variable
                                                       └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 140
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Leaf
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 140
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 153
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Leaf
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 153
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 140
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fork
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 140
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 140
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 140
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 140
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 140
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 140
                                                          └──Desc: Variable: t1
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 140
                                                          └──Desc: Variable: t2
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 153
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fork
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 153
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 153
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 153
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 153
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 153
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 153
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 140
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 153
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: 140
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 153
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 140
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 153
                                                                      └──Desc: Variable
                                                                         └──Variable: pre_subst
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: 140
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: 153
                                                                      └──Desc: Variable
                                                                         └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 140
                                                                └──Desc: Variable
                                                                   └──Variable: t1
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 153
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 140
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 153
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: 140
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 153
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 140
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 153
                                                                      └──Desc: Variable
                                                                         └──Variable: pre_subst
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: 140
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: 153
                                                                      └──Desc: Variable
                                                                         └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 140
                                                                └──Desc: Variable
                                                                   └──Variable: t2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: 207
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 209
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 181
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 207
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 181
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 209
                   └──Desc: Variable: comp_subst
                └──Abstraction:
                   └──Variables: 181
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 207
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 209
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 181
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 207
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 181
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 209
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 207
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 209
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: 181
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 207
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: 181
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 209
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Variable: 181
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: 207
                                  └──Desc: Variable: g
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Variable: 181
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: 209
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: 181
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: 209
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 207
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 209
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 207
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 209
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 207
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 209
                                                    └──Desc: Variable
                                                       └──Variable: pre_subst
                                                       └──Type expr: Variable: 209
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 207
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 209
                                                    └──Desc: Variable
                                                       └──Variable: f
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 207
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 181
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 207
                                                    └──Desc: Variable
                                                       └──Variable: g
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 181
                                                    └──Desc: Variable
                                                       └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: thin
                └──Abstraction:
                   └──Variables: 231
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 263
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 263
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 263
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 263
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 263
                               └──Type expr: Constructor: fin
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: 263
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: 263
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: 263
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Variable: 263
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: 263
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 263
                                              └──Desc: Variable
                                                 └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: 263
                                              └──Desc: Variable
                                                 └──Variable: y
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 263
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: 263
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 263
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 263
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 263
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 263
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 263
                                                    └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 263
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fin_succ
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 263
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 263
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 263
                                                    └──Desc: Variable
                                                       └──Variable: y
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 263
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 263
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 263
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 335
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 263
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 335
                                                          └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 263
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 263
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 263
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fin_zero
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: unit
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 263
                                                 └──Expression:
                                                    └──Type expr: Constructor: unit
                                                    └──Desc: Constant: ()
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 263
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 263
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 263
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 375
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 263
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 375
                                                          └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 263
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 372
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 263
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 372
                                                          └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 263
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fin_succ
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 263
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 263
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 263
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 372
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 263
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: 375
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: 372
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: 263
                                                                └──Desc: Variable
                                                                   └──Variable: thin
                                                                   └──Type expr: Variable: 372
                                                             └──Expression:
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: 375
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 372
                                                          └──Desc: Variable
                                                             └──Variable: y
       └──Structure item: Type
          └──Type declaration:
             └──Type name: option
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: None
                   └──Constructor alphas: 395
                   └──Constructor type:
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: 395
                └──Constructor declaration:
                   └──Constructor name: Some
                   └──Constructor alphas: 395
                   └──Constructor type:
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: 395
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: 395
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: 444
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: 444
                            └──Type expr: Constructor: option
                               └──Type expr: Variable: 438
                         └──Type expr: Constructor: option
                            └──Type expr: Variable: 438
                   └──Desc: Variable: bind
                └──Abstraction:
                   └──Variables: 444,444,444
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: option
                            └──Type expr: Variable: 444
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: 444
                               └──Type expr: Constructor: option
                                  └──Type expr: Variable: 438
                            └──Type expr: Constructor: option
                               └──Type expr: Variable: 438
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: option
                               └──Type expr: Variable: 444
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 444
                                  └──Type expr: Constructor: option
                                     └──Type expr: Variable: 438
                               └──Type expr: Constructor: option
                                  └──Type expr: Variable: 438
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 444
                                     └──Type expr: Constructor: option
                                        └──Type expr: Variable: 438
                                  └──Desc: Variable: f
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Variable: 438
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: option
                                           └──Type expr: Variable: 444
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Constructor: option
                                        └──Type expr: Variable: 444
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Variable: 444
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: None
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Variable: 444
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Variable: 438
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: None
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Variable: 438
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Variable: 444
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Some
                                                    └──Constructor argument type:
                                                       └──Type expr: Variable: 444
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Variable: 444
                                                 └──Pattern:
                                                    └──Type expr: Variable: 444
                                                    └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Variable: 438
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 444
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Variable: 438
                                                    └──Desc: Variable
                                                       └──Variable: f
                                                 └──Expression:
                                                    └──Type expr: Variable: 444
                                                    └──Desc: Variable
                                                       └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: thick
                └──Abstraction:
                   └──Variables: 464
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 498
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 498
                            └──Type expr: Constructor: option
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 498
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 498
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: 498
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: 498
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: 498
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Variable: 498
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Variable: 498
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Variable: 498
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 498
                                              └──Desc: Variable
                                                 └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 498
                                              └──Desc: Variable
                                                 └──Variable: y
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 498
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 498
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 498
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 498
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 498
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 498
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 498
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 498
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 498
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: None
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 498
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 498
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 498
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 498
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 498
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 498
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 576
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 498
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 576
                                                          └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 498
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Some
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 498
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 498
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 498
                                                    └──Desc: Variable
                                                       └──Variable: y
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 498
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 498
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 498
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 614
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 498
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 614
                                                          └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 498
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 498
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 498
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Constructor: is_succ
                                                       └──Type expr: Variable: 614
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 614
                                                             └──Type expr: Constructor: is_succ
                                                                └──Type expr: Variable: 614
                                                          └──Desc: Variable
                                                             └──Variable: fin_succ
                                                             └──Type expr: Variable: 614
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 614
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Type expr: Constructor: is_succ
                                                    └──Type expr: Variable: 614
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Constructor: is_succ
                                                             └──Type expr: Variable: 614
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Is_succ
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: unit
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: is_succ
                                                                      └──Type expr: Variable: 614
                                                             └──Pattern:
                                                                └──Type expr: Constructor: unit
                                                                └──Desc: Constant: ()
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 498
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Some
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: 498
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: 498
                                                             └──Expression:
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: 498
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Fin_zero
                                                                      └──Constructor argument type:
                                                                         └──Type expr: Constructor: unit
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: 498
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: unit
                                                                      └──Desc: Constant: ()
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 498
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 498
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 498
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 692
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 498
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 692
                                                          └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 498
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 689
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 498
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 689
                                                          └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 498
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Constructor: is_succ
                                                       └──Type expr: Variable: 692
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 692
                                                             └──Type expr: Constructor: is_succ
                                                                └──Type expr: Variable: 692
                                                          └──Desc: Variable
                                                             └──Variable: fin_succ
                                                             └──Type expr: Variable: 692
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 692
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Type expr: Constructor: is_succ
                                                    └──Type expr: Variable: 692
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Constructor: is_succ
                                                             └──Type expr: Variable: 692
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Is_succ
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: unit
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: is_succ
                                                                      └──Type expr: Variable: 692
                                                             └──Pattern:
                                                                └──Type expr: Constructor: unit
                                                                └──Desc: Constant: ()
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 498
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: 793
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: 498
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: 498
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: option
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: 793
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Variable: 793
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Variable: 498
                                                                            └──Type expr: Constructor: option
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Variable: 498
                                                                      └──Desc: Variable
                                                                         └──Variable: bind
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: 793
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: 793
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Variable: 689
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Variable: 793
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: fin
                                                                                        └──Type expr: Variable: 692
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: fin
                                                                                           └──Type expr: Variable: 689
                                                                                        └──Type expr: Constructor: option
                                                                                           └──Type expr: Constructor: fin
                                                                                              └──Type expr: Variable: 793
                                                                                  └──Desc: Variable
                                                                                     └──Variable: thick
                                                                                     └──Type expr: Variable: 793
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Variable: 692
                                                                                  └──Desc: Variable
                                                                                     └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: 689
                                                                            └──Desc: Variable
                                                                               └──Variable: y
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: 793
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: 498
                                                                └──Desc: Function
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: 793
                                                                      └──Desc: Variable: x
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: 498
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Some
                                                                            └──Constructor argument type:
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Variable: 498
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Variable: 498
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: 498
                                                                            └──Desc: Construct
                                                                               └──Constructor description:
                                                                                  └──Name: Fin_succ
                                                                                  └──Constructor argument type:
                                                                                     └──Type expr: Constructor: fin
                                                                                        └──Type expr: Variable: 793
                                                                                  └──Constructor type:
                                                                                     └──Type expr: Constructor: fin
                                                                                        └──Type expr: Variable: 498
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Variable: 793
                                                                                  └──Desc: Variable
                                                                                     └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: check
                └──Abstraction:
                   └──Variables: 817
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 851
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 851
                            └──Type expr: Constructor: option
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 851
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 851
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: 851
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 851
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: 851
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: 851
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: term
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 851
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Constructor: term
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: 851
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 851
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 851
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 851
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 851
                                                    └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 851
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 851
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 851
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 851
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: 851
                                                             └──Type expr: Arrow
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: 851
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 851
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 851
                                                          └──Desc: Variable
                                                             └──Variable: bind
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 851
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 851
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Constructor: succ
                                                                         └──Type expr: Variable: 851
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: 851
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Constructor: succ
                                                                               └──Type expr: Variable: 851
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Constructor: succ
                                                                                  └──Type expr: Variable: 851
                                                                            └──Type expr: Constructor: option
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Variable: 851
                                                                      └──Desc: Variable
                                                                         └──Variable: thick
                                                                         └──Type expr: Variable: 851
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: 851
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: 851
                                                                └──Desc: Variable
                                                                   └──Variable: y
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 851
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 851
                                                    └──Desc: Function
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 851
                                                          └──Desc: Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 851
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Some
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 851
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 851
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 851
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Var
                                                                      └──Constructor argument type:
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: 851
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: 851
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: 851
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 851
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Leaf
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 851
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 851
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Some
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 851
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 851
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 851
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Leaf
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 851
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 851
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fork
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 851
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 851
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 851
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 851
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 851
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 851
                                                          └──Desc: Variable: t1
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 851
                                                          └──Desc: Variable: t2
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 851
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 851
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 851
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 851
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 851
                                                             └──Type expr: Arrow
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 851
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 851
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 851
                                                          └──Desc: Variable
                                                             └──Variable: bind
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 851
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 851
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Constructor: succ
                                                                         └──Type expr: Variable: 851
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 851
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Constructor: succ
                                                                               └──Type expr: Variable: 851
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Constructor: succ
                                                                                  └──Type expr: Variable: 851
                                                                            └──Type expr: Constructor: option
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Variable: 851
                                                                      └──Desc: Variable
                                                                         └──Variable: check
                                                                         └──Type expr: Variable: 851
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: 851
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: 851
                                                                └──Desc: Variable
                                                                   └──Variable: t1
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 851
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 851
                                                    └──Desc: Function
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 851
                                                          └──Desc: Variable: t1
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 851
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 851
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: 851
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 851
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: option
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 851
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Variable: 851
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: term
                                                                                     └──Type expr: Variable: 851
                                                                            └──Type expr: Constructor: option
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Variable: 851
                                                                      └──Desc: Variable
                                                                         └──Variable: bind
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: 851
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: 851
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Constructor: succ
                                                                                     └──Type expr: Variable: 851
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: term
                                                                                     └──Type expr: Variable: 851
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: fin
                                                                                        └──Type expr: Constructor: succ
                                                                                           └──Type expr: Variable: 851
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Constructor: succ
                                                                                              └──Type expr: Variable: 851
                                                                                        └──Type expr: Constructor: option
                                                                                           └──Type expr: Constructor: term
                                                                                              └──Type expr: Variable: 851
                                                                                  └──Desc: Variable
                                                                                     └──Variable: check
                                                                                     └──Type expr: Variable: 851
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Constructor: succ
                                                                                        └──Type expr: Variable: 851
                                                                                  └──Desc: Variable
                                                                                     └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Constructor: succ
                                                                                  └──Type expr: Variable: 851
                                                                            └──Desc: Variable
                                                                               └──Variable: t2
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 851
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 851
                                                                └──Desc: Function
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 851
                                                                      └──Desc: Variable: t2
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: 851
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Some
                                                                            └──Constructor argument type:
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Variable: 851
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: term
                                                                                     └──Type expr: Variable: 851
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 851
                                                                            └──Desc: Construct
                                                                               └──Constructor description:
                                                                                  └──Name: Fork
                                                                                  └──Constructor argument type:
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Variable: 851
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Variable: 851
                                                                                  └──Constructor type:
                                                                                     └──Type expr: Constructor: term
                                                                                        └──Type expr: Variable: 851
                                                                               └──Expression:
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Constructor: term
                                                                                        └──Type expr: Variable: 851
                                                                                     └──Type expr: Constructor: term
                                                                                        └──Type expr: Variable: 851
                                                                                  └──Desc: Tuple
                                                                                     └──Expression:
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Variable: 851
                                                                                        └──Desc: Variable
                                                                                           └──Variable: t1
                                                                                     └──Expression:
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Variable: 851
                                                                                        └──Desc: Variable
                                                                                           └──Variable: t2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: fin
                         └──Type expr: Constructor: succ
                            └──Type expr: Variable: 1106
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 1106
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 1106
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 1106
                   └──Desc: Variable: subst_var
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 1106
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 1106
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: 1106
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 1106
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 1106
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 1106
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: 1106
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 1106
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 1106
                                  └──Desc: Variable: t'
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: 1106
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: 1106
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 1106
                                        └──Desc: Variable: y
                                     └──Expression:
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: 1106
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 1106
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 1106
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 1106
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 1106
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: 1106
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: 1106
                                                          └──Desc: Variable
                                                             └──Variable: thick
                                                             └──Type expr: Variable: 1106
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 1106
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 1106
                                                    └──Desc: Variable
                                                       └──Variable: y
                                           └──Type expr: Constructor: option
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: 1106
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 1106
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: None
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: 1106
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 1106
                                                    └──Desc: Variable
                                                       └──Variable: t'
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 1106
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Some
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 1106
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: 1106
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 1106
                                                          └──Desc: Variable: y'
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 1106
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Var
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 1106
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 1106
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 1106
                                                          └──Desc: Variable
                                                             └──Variable: y'
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: fin
                         └──Type expr: Constructor: succ
                            └──Type expr: Variable: 1128
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 1128
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 1128
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 1128
                   └──Desc: Variable: subst
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 1128
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 1128
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: 1128
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 1128
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 1128
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 1128
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: term
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: 1128
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 1128
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 1128
                                  └──Desc: Variable: t'
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: term
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: 1128
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: 1128
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 1128
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 1128
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 1128
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 1128
                                        └──Desc: Variable
                                           └──Variable: pre_subst
                                           └──Type expr: Variable: 1128
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Variable: 1128
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: 1128
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 1128
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 1128
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 1128
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 1128
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 1128
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 1128
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 1128
                                                    └──Desc: Variable
                                                       └──Variable: subst_var
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 1128
                                                    └──Desc: Variable
                                                       └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 1128
                                              └──Desc: Variable
                                                 └──Variable: t'
       └──Structure item: Type
          └──Type declaration:
             └──Type name: alist
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Anil
                   └──Constructor alphas: 398 399
                   └──Constructor type:
                      └──Type expr: Constructor: alist
                         └──Type expr: Variable: 398
                         └──Type expr: Variable: 399
                   └──Constraint:
                      └──Type expr: Variable: 398
                      └──Type expr: Variable: 399
                └──Constructor declaration:
                   └──Constructor name: Asnoc
                   └──Constructor alphas: 398 399
                   └──Constructor type:
                      └──Type expr: Constructor: alist
                         └──Type expr: Variable: 398
                         └──Type expr: Variable: 399
                   └──Constructor argument:
                      └──Constructor betas: 401
                      └──Type expr: Tuple
                         └──Type expr: Constructor: alist
                            └──Type expr: Variable: 401
                            └──Type expr: Variable: 399
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 401
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 401
                   └──Constraint:
                      └──Type expr: Variable: 398
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: 401
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: sub
                └──Abstraction:
                   └──Variables: 1158,1157
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: alist
                            └──Type expr: Variable: 1185
                            └──Type expr: Variable: 1186
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 1185
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 1186
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: 1185
                               └──Type expr: Variable: 1186
                            └──Desc: Variable: s
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 1185
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 1186
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: alist
                                     └──Type expr: Variable: 1185
                                     └──Type expr: Variable: 1186
                                  └──Desc: Variable
                                     └──Variable: s
                               └──Type expr: Constructor: alist
                                  └──Type expr: Variable: 1185
                                  └──Type expr: Variable: 1186
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Variable: 1185
                                           └──Type expr: Variable: 1186
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Anil
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: 1185
                                                    └──Type expr: Variable: 1186
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: 1185
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: 1186
                                        └──Desc: Variable
                                           └──Variable: var
                                           └──Type expr: Variable: 1185
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Variable: 1185
                                           └──Type expr: Variable: 1186
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Asnoc
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: 1251
                                                       └──Type expr: Variable: 1186
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 1251
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 1251
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: 1185
                                                    └──Type expr: Variable: 1186
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: 1251
                                                    └──Type expr: Variable: 1186
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 1251
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 1251
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: 1251
                                                       └──Type expr: Variable: 1186
                                                    └──Desc: Variable: s
                                                 └──Pattern:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 1251
                                                    └──Desc: Variable: t
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 1251
                                                    └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: 1185
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: 1186
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 1185
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 1251
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 1185
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 1186
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 1251
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 1186
                                                       └──Type expr: Arrow
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 1185
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 1251
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 1185
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 1186
                                                    └──Desc: Variable
                                                       └──Variable: comp_subst
                                                       └──Type expr: Variable: 1185
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 1251
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 1186
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: alist
                                                                └──Type expr: Variable: 1251
                                                                └──Type expr: Variable: 1186
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: 1251
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 1186
                                                          └──Desc: Variable
                                                             └──Variable: sub
                                                             └──Type expr: Variable: 1186
                                                             └──Type expr: Variable: 1251
                                                       └──Expression:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: 1251
                                                             └──Type expr: Variable: 1186
                                                          └──Desc: Variable
                                                             └──Variable: s
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 1185
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 1251
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 1251
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 1185
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 1251
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 1251
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 1251
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: 1185
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 1251
                                                          └──Desc: Variable
                                                             └──Variable: subst_var
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 1251
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 1251
                                                    └──Desc: Variable
                                                       └──Variable: t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: append
                └──Abstraction:
                   └──Variables: 1339,1343,1342
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: alist
                            └──Type expr: Variable: 1373
                            └──Type expr: Variable: 1374
                         └──Type expr: Arrow
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: 1385
                               └──Type expr: Variable: 1373
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: 1385
                               └──Type expr: Variable: 1374
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: 1373
                               └──Type expr: Variable: 1374
                            └──Desc: Variable: s1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: alist
                                  └──Type expr: Variable: 1385
                                  └──Type expr: Variable: 1373
                               └──Type expr: Constructor: alist
                                  └──Type expr: Variable: 1385
                                  └──Type expr: Variable: 1374
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: alist
                                     └──Type expr: Variable: 1385
                                     └──Type expr: Variable: 1373
                                  └──Desc: Variable: s2
                               └──Expression:
                                  └──Type expr: Constructor: alist
                                     └──Type expr: Variable: 1385
                                     └──Type expr: Variable: 1374
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Variable: 1385
                                           └──Type expr: Variable: 1373
                                        └──Desc: Variable
                                           └──Variable: s2
                                     └──Type expr: Constructor: alist
                                        └──Type expr: Variable: 1385
                                        └──Type expr: Variable: 1373
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: 1385
                                                 └──Type expr: Variable: 1373
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Anil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: 1385
                                                          └──Type expr: Variable: 1373
                                           └──Expression:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: 1385
                                                 └──Type expr: Variable: 1374
                                              └──Desc: Variable
                                                 └──Variable: s1
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: 1385
                                                 └──Type expr: Variable: 1373
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Asnoc
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: 1434
                                                             └──Type expr: Variable: 1373
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 1434
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 1434
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: 1385
                                                          └──Type expr: Variable: 1373
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: 1434
                                                          └──Type expr: Variable: 1373
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 1434
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 1434
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: 1434
                                                             └──Type expr: Variable: 1373
                                                          └──Desc: Variable: s2
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 1434
                                                          └──Desc: Variable: t
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 1434
                                                          └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: 1385
                                                 └──Type expr: Variable: 1374
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Asnoc
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: 1434
                                                             └──Type expr: Variable: 1374
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 1434
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 1434
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: 1385
                                                          └──Type expr: Variable: 1374
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: 1434
                                                          └──Type expr: Variable: 1374
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 1434
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 1434
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: 1434
                                                             └──Type expr: Variable: 1374
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: alist
                                                                      └──Type expr: Variable: 1434
                                                                      └──Type expr: Variable: 1373
                                                                   └──Type expr: Constructor: alist
                                                                      └──Type expr: Variable: 1434
                                                                      └──Type expr: Variable: 1374
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: alist
                                                                            └──Type expr: Variable: 1373
                                                                            └──Type expr: Variable: 1374
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: alist
                                                                               └──Type expr: Variable: 1434
                                                                               └──Type expr: Variable: 1373
                                                                            └──Type expr: Constructor: alist
                                                                               └──Type expr: Variable: 1434
                                                                               └──Type expr: Variable: 1374
                                                                      └──Desc: Variable
                                                                         └──Variable: append
                                                                         └──Type expr: Variable: 1434
                                                                         └──Type expr: Variable: 1374
                                                                         └──Type expr: Variable: 1373
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: alist
                                                                         └──Type expr: Variable: 1373
                                                                         └──Type expr: Variable: 1374
                                                                      └──Desc: Variable
                                                                         └──Variable: s1
                                                             └──Expression:
                                                                └──Type expr: Constructor: alist
                                                                   └──Type expr: Variable: 1434
                                                                   └──Type expr: Variable: 1373
                                                                └──Desc: Variable
                                                                   └──Variable: s2
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 1434
                                                          └──Desc: Variable
                                                             └──Variable: t
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 1434
                                                          └──Desc: Variable
                                                             └──Variable: x
       └──Structure item: Type
          └──Type declaration:
             └──Type name: ex_alist
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Exists_alist
                   └──Constructor alphas: 409
                   └──Constructor type:
                      └──Type expr: Constructor: ex_alist
                         └──Type expr: Variable: 409
                   └──Constructor argument:
                      └──Constructor betas: 410
                      └──Type expr: Constructor: alist
                         └──Type expr: Variable: 409
                         └──Type expr: Variable: 410
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: alist
                         └──Type expr: Variable: 1521
                         └──Type expr: Variable: 1520
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 1521
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 1521
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 1521
                   └──Desc: Variable: asnoc
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: alist
                            └──Type expr: Variable: 1521
                            └──Type expr: Variable: 1520
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 1521
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: 1521
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: 1521
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: 1521
                               └──Type expr: Variable: 1520
                            └──Desc: Variable: a
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 1521
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: 1521
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: 1521
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 1521
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: 1521
                                     └──Type expr: Constructor: ex_alist
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: 1521
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 1521
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 1521
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Exists_alist
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 1521
                                                    └──Type expr: Variable: 1520
                                              └──Constructor type:
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 1521
                                           └──Expression:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 1521
                                                 └──Type expr: Variable: 1520
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Asnoc
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: 1521
                                                             └──Type expr: Variable: 1520
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 1521
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 1521
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 1521
                                                          └──Type expr: Variable: 1520
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: 1521
                                                          └──Type expr: Variable: 1520
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 1521
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 1521
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: 1521
                                                             └──Type expr: Variable: 1520
                                                          └──Desc: Variable
                                                             └──Variable: a
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 1521
                                                          └──Desc: Variable
                                                             └──Variable: t
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 1521
                                                          └──Desc: Variable
                                                             └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: weaken_fin
                └──Abstraction:
                   └──Variables: 1549
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: 1570
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 1570
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 1570
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 1570
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: 1570
                                  └──Desc: Variable
                                     └──Variable: f
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 1570
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: 1570
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_zero
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 1570
                                           └──Pattern:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
                                     └──Expression:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 1570
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_zero
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 1570
                                           └──Expression:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: 1570
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 1616
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 1570
                                           └──Pattern:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: 1616
                                              └──Desc: Variable: f
                                     └──Expression:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 1570
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 1570
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 1570
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: 1570
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 1616
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 1570
                                                    └──Desc: Variable
                                                       └──Variable: weaken_fin
                                                       └──Type expr: Variable: 1616
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 1616
                                                    └──Desc: Variable
                                                       └──Variable: f
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: term
                         └──Type expr: Variable: 1685
                      └──Type expr: Constructor: term
                         └──Type expr: Constructor: succ
                            └──Type expr: Variable: 1685
                   └──Desc: Variable: weaken_term
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 1685
                         └──Type expr: Constructor: term
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 1685
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 1685
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: term
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 1685
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: 1685
                                     └──Type expr: Constructor: term
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: 1685
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: 1685
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 1685
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 1685
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 1685
                                        └──Desc: Variable
                                           └──Variable: pre_subst
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 1685
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: 1685
                                           └──Type expr: Constructor: term
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Variable: 1685
                                        └──Desc: Function
                                           └──Pattern:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: 1685
                                              └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 1685
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 1685
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 1685
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 1685
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 1685
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 1685
                                                          └──Desc: Variable
                                                             └──Variable: weaken_fin
                                                             └──Type expr: Variable: 1685
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 1685
                                                          └──Desc: Variable
                                                             └──Variable: x
                               └──Expression:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 1685
                                  └──Desc: Variable
                                     └──Variable: t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: weaken_alist
                └──Abstraction:
                   └──Variables: 1700,1699
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: alist
                            └──Type expr: Variable: 1727
                            └──Type expr: Variable: 1728
                         └──Type expr: Constructor: alist
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 1727
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 1728
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: 1727
                               └──Type expr: Variable: 1728
                            └──Desc: Variable: s
                         └──Expression:
                            └──Type expr: Constructor: alist
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 1727
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 1728
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: alist
                                     └──Type expr: Variable: 1727
                                     └──Type expr: Variable: 1728
                                  └──Desc: Variable
                                     └──Variable: s
                               └──Type expr: Constructor: alist
                                  └──Type expr: Variable: 1727
                                  └──Type expr: Variable: 1728
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Variable: 1727
                                           └──Type expr: Variable: 1728
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Anil
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: 1727
                                                    └──Type expr: Variable: 1728
                                     └──Expression:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 1727
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 1728
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Anil
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 1727
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 1727
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Variable: 1727
                                           └──Type expr: Variable: 1728
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Asnoc
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: 1793
                                                       └──Type expr: Variable: 1728
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 1793
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 1793
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: 1727
                                                    └──Type expr: Variable: 1728
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: 1793
                                                    └──Type expr: Variable: 1728
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 1793
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 1793
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: 1793
                                                       └──Type expr: Variable: 1728
                                                    └──Desc: Variable: s
                                                 └──Pattern:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 1793
                                                    └──Desc: Variable: t
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 1793
                                                    └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 1727
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 1728
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Asnoc
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: 1727
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 1728
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 1727
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 1727
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 1727
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 1728
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: 1727
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 1728
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 1727
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 1727
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: 1727
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 1728
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: alist
                                                                └──Type expr: Variable: 1793
                                                                └──Type expr: Variable: 1728
                                                             └──Type expr: Constructor: alist
                                                                └──Type expr: Variable: 1727
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 1728
                                                          └──Desc: Variable
                                                             └──Variable: weaken_alist
                                                             └──Type expr: Variable: 1728
                                                             └──Type expr: Variable: 1793
                                                       └──Expression:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: 1793
                                                             └──Type expr: Variable: 1728
                                                          └──Desc: Variable
                                                             └──Variable: s
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 1727
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 1793
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 1727
                                                          └──Desc: Variable
                                                             └──Variable: weaken_term
                                                             └──Type expr: Variable: 1793
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 1793
                                                          └──Desc: Variable
                                                             └──Variable: t
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 1727
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 1727
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 1727
                                                          └──Desc: Variable
                                                             └──Variable: weaken_fin
                                                             └──Type expr: Variable: 1727
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 1727
                                                          └──Desc: Variable
                                                             └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: sub'
                └──Abstraction:
                   └──Variables: 1892
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ex_alist
                            └──Type expr: Variable: 1916
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 1916
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 1916
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Variable: 1916
                            └──Desc: Variable: e
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 1916
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 1916
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Variable: 1916
                                  └──Desc: Variable
                                     └──Variable: e
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Variable: 1916
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: 1916
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Exists_alist
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: 1916
                                                    └──Type expr: Variable: 1941
                                              └──Constructor type:
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Variable: 1916
                                           └──Pattern:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: 1916
                                                 └──Type expr: Variable: 1941
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Anil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: 1916
                                                          └──Type expr: Variable: 1941
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: 1916
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: 1916
                                        └──Desc: Variable
                                           └──Variable: var
                                           └──Type expr: Variable: 1916
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: 1916
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Exists_alist
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: 1916
                                                    └──Type expr: Variable: 1972
                                              └──Constructor type:
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Variable: 1916
                                           └──Pattern:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: 1916
                                                 └──Type expr: Variable: 1972
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Asnoc
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: 1991
                                                             └──Type expr: Variable: 1972
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 1991
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 1991
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: 1916
                                                          └──Type expr: Variable: 1972
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: 1991
                                                          └──Type expr: Variable: 1972
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 1991
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 1991
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: 1991
                                                             └──Type expr: Variable: 1972
                                                          └──Desc: Variable: s
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 1991
                                                          └──Desc: Variable: t
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 1991
                                                          └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: 1916
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: 1916
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 1916
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 1916
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 1916
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 1916
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 1916
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 1916
                                                       └──Type expr: Arrow
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 1916
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 1916
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 1916
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 1916
                                                    └──Desc: Variable
                                                       └──Variable: comp_subst
                                                       └──Type expr: Variable: 1916
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 1916
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 1916
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: ex_alist
                                                                └──Type expr: Variable: 1916
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: 1916
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 1916
                                                          └──Desc: Variable
                                                             └──Variable: sub'
                                                             └──Type expr: Variable: 1916
                                                       └──Expression:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: 1916
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Exists_alist
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: alist
                                                                      └──Type expr: Variable: 1916
                                                                      └──Type expr: Constructor: succ
                                                                         └──Type expr: Variable: 1972
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: ex_alist
                                                                      └──Type expr: Variable: 1916
                                                             └──Expression:
                                                                └──Type expr: Constructor: alist
                                                                   └──Type expr: Variable: 1916
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: 1972
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: alist
                                                                            └──Type expr: Variable: 1991
                                                                            └──Type expr: Variable: 1972
                                                                         └──Type expr: Constructor: alist
                                                                            └──Type expr: Variable: 1916
                                                                            └──Type expr: Constructor: succ
                                                                               └──Type expr: Variable: 1972
                                                                      └──Desc: Variable
                                                                         └──Variable: weaken_alist
                                                                         └──Type expr: Variable: 1972
                                                                         └──Type expr: Variable: 1991
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: alist
                                                                         └──Type expr: Variable: 1991
                                                                         └──Type expr: Variable: 1972
                                                                      └──Desc: Variable
                                                                         └──Variable: s
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 1916
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 1916
                                              └──Desc: Function
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 1916
                                                    └──Desc: Variable: t'
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 1916
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 1991
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 1916
                                                          └──Desc: Variable
                                                             └──Variable: weaken_term
                                                             └──Type expr: Variable: 1991
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 1991
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: 1916
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 1991
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: 1991
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: 1916
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 1991
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Constructor: succ
                                                                                     └──Type expr: Variable: 1991
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: term
                                                                                     └──Type expr: Variable: 1991
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: fin
                                                                                        └──Type expr: Variable: 1916
                                                                                     └──Type expr: Constructor: term
                                                                                        └──Type expr: Variable: 1991
                                                                            └──Desc: Variable
                                                                               └──Variable: subst_var
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Constructor: succ
                                                                                  └──Type expr: Variable: 1991
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 1991
                                                                      └──Desc: Variable
                                                                         └──Variable: t
                                                             └──Expression:
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: 1916
                                                                └──Desc: Variable
                                                                   └──Variable: t'
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: ex_alist
                         └──Type expr: Variable: 2119
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 2119
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 2119
                   └──Desc: Variable: subst'
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ex_alist
                            └──Type expr: Variable: 2119
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 2119
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 2119
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Variable: 2119
                            └──Desc: Variable: e
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 2119
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 2119
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Arrow
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: 2119
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: 2119
                                     └──Type expr: Arrow
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: 2119
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: 2119
                                  └──Desc: Variable
                                     └──Variable: pre_subst
                                     └──Type expr: Variable: 2119
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Variable: 2119
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: 2119
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: ex_alist
                                              └──Type expr: Variable: 2119
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: 2119
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 2119
                                        └──Desc: Variable
                                           └──Variable: sub'
                                           └──Type expr: Variable: 2119
                                     └──Expression:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: 2119
                                        └──Desc: Variable
                                           └──Variable: e
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: fin
                         └──Type expr: Constructor: succ
                            └──Type expr: Variable: 2183
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 2183
                         └──Type expr: Constructor: ex_alist
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 2183
                   └──Desc: Variable: flex_flex
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 2183
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 2183
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 2183
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 2183
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: 2183
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: 2183
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: 2183
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: 2183
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: option
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: 2183
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 2183
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 2183
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 2183
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 2183
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 2183
                                                    └──Desc: Variable
                                                       └──Variable: thick
                                                       └──Type expr: Variable: 2183
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 2183
                                                    └──Desc: Variable
                                                       └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 2183
                                              └──Desc: Variable
                                                 └──Variable: y
                                     └──Type expr: Constructor: option
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: 2183
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 2183
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Some
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 2183
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 2183
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 2183
                                                    └──Desc: Variable: y'
                                           └──Expression:
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 2183
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 2183
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 2183
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 2183
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: 2183
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: 2183
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: alist
                                                                      └──Type expr: Variable: 2183
                                                                      └──Type expr: Variable: 2183
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 2183
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Constructor: succ
                                                                               └──Type expr: Variable: 2183
                                                                         └──Type expr: Constructor: ex_alist
                                                                            └──Type expr: Constructor: succ
                                                                               └──Type expr: Variable: 2183
                                                                └──Desc: Variable
                                                                   └──Variable: asnoc
                                                                   └──Type expr: Variable: 2183
                                                                   └──Type expr: Variable: 2183
                                                             └──Expression:
                                                                └──Type expr: Constructor: alist
                                                                   └──Type expr: Variable: 2183
                                                                   └──Type expr: Variable: 2183
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Anil
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: alist
                                                                            └──Type expr: Variable: 2183
                                                                            └──Type expr: Variable: 2183
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 2183
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Var
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: 2183
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 2183
                                                             └──Expression:
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: 2183
                                                                └──Desc: Variable
                                                                   └──Variable: y'
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 2183
                                                    └──Desc: Variable
                                                       └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 2183
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: None
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 2183
                                           └──Expression:
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 2183
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Exists_alist
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 2183
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 2183
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 2183
                                                 └──Expression:
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 2183
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 2183
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Anil
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: alist
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 2183
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 2183
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: fin
                         └──Type expr: Constructor: succ
                            └──Type expr: Variable: 2265
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 2265
                         └──Type expr: Constructor: option
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 2265
                   └──Desc: Variable: flex_rigid
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 2265
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 2265
                            └──Type expr: Constructor: option
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: 2265
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 2265
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: 2265
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: 2265
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: 2265
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Constructor: ex_alist
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: 2265
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 2265
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 2265
                                           └──Type expr: Constructor: option
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 2265
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 2265
                                                 └──Type expr: Arrow
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 2265
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 2265
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 2265
                                              └──Desc: Variable
                                                 └──Variable: bind
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 2265
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 2265
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 2265
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 2265
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 2265
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: 2265
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 2265
                                                          └──Desc: Variable
                                                             └──Variable: check
                                                             └──Type expr: Variable: 2265
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 2265
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 2265
                                                    └──Desc: Variable
                                                       └──Variable: t
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: 2265
                                           └──Type expr: Constructor: option
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 2265
                                        └──Desc: Function
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 2265
                                              └──Desc: Variable: t'
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 2265
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Some
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 2265
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 2265
                                                 └──Expression:
                                                    └──Type expr: Constructor: ex_alist
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 2265
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 2265
                                                             └──Type expr: Constructor: ex_alist
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 2265
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 2265
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: 2265
                                                                      └──Type expr: Constructor: ex_alist
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: 2265
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: alist
                                                                            └──Type expr: Variable: 2265
                                                                            └──Type expr: Variable: 2265
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 2265
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Constructor: succ
                                                                                     └──Type expr: Variable: 2265
                                                                               └──Type expr: Constructor: ex_alist
                                                                                  └──Type expr: Constructor: succ
                                                                                     └──Type expr: Variable: 2265
                                                                      └──Desc: Variable
                                                                         └──Variable: asnoc
                                                                         └──Type expr: Variable: 2265
                                                                         └──Type expr: Variable: 2265
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: alist
                                                                         └──Type expr: Variable: 2265
                                                                         └──Type expr: Variable: 2265
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Anil
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: alist
                                                                                  └──Type expr: Variable: 2265
                                                                                  └──Type expr: Variable: 2265
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 2265
                                                                └──Desc: Variable
                                                                   └──Variable: t'
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 2265
                                                          └──Desc: Variable
                                                             └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: amgu
                └──Abstraction:
                   └──Variables: 2287
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 2318
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 2318
                            └──Type expr: Arrow
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Variable: 2318
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Variable: 2318
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 2318
                            └──Desc: Variable: s
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 2318
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Variable: 2318
                                  └──Type expr: Constructor: option
                                     └──Type expr: Constructor: ex_alist
                                        └──Type expr: Variable: 2318
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 2318
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: ex_alist
                                        └──Type expr: Variable: 2318
                                     └──Type expr: Constructor: option
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: 2318
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: 2318
                                        └──Desc: Variable: acc
                                     └──Expression:
                                        └──Type expr: Constructor: option
                                           └──Type expr: Constructor: ex_alist
                                              └──Type expr: Variable: 2318
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 2318
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 2318
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Variable: 2318
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 2318
                                                    └──Desc: Variable
                                                       └──Variable: s
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 2318
                                                    └──Desc: Variable
                                                       └──Variable: t
                                                 └──Expression:
                                                    └──Type expr: Constructor: ex_alist
                                                       └──Type expr: Variable: 2318
                                                    └──Desc: Variable
                                                       └──Variable: acc
                                           └──Type expr: Tuple
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 2318
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 2318
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Variable: 2318
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 2318
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 2318
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: 2318
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 2318
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Leaf
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 2318
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 2318
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Leaf
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 2318
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: 2318
                                                          └──Desc: Any
                                                 └──Expression:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: 2318
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Some
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: ex_alist
                                                                └──Type expr: Variable: 2318
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: 2318
                                                       └──Expression:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: 2318
                                                          └──Desc: Variable
                                                             └──Variable: acc
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 2318
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 2318
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: 2318
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 2318
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Leaf
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 2318
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 2318
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Fork
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 2318
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 2318
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 2318
                                                             └──Pattern:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 2318
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 2318
                                                                └──Desc: Any
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: 2318
                                                          └──Desc: Any
                                                 └──Expression:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: 2318
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: None
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: 2318
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 2318
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 2318
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: 2318
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 2318
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Fork
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 2318
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 2318
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 2318
                                                             └──Pattern:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 2318
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 2318
                                                                └──Desc: Any
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 2318
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Leaf
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 2318
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: 2318
                                                          └──Desc: Any
                                                 └──Expression:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: 2318
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: None
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: 2318
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 2318
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 2318
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: 2318
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 2318
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Fork
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 2318
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 2318
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 2318
                                                             └──Pattern:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 2318
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 2318
                                                                └──Desc: Tuple
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 2318
                                                                      └──Desc: Variable: s1
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 2318
                                                                      └──Desc: Variable: s2
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 2318
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Fork
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 2318
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 2318
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 2318
                                                             └──Pattern:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 2318
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 2318
                                                                └──Desc: Tuple
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 2318
                                                                      └──Desc: Variable: t1
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 2318
                                                                      └──Desc: Variable: t2
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: 2318
                                                          └──Desc: Any
                                                 └──Expression:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: 2318
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: 2318
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: ex_alist
                                                                      └──Type expr: Variable: 2318
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: 2318
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: ex_alist
                                                                         └──Type expr: Variable: 2318
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ex_alist
                                                                            └──Type expr: Variable: 2318
                                                                         └──Type expr: Constructor: option
                                                                            └──Type expr: Constructor: ex_alist
                                                                               └──Type expr: Variable: 2318
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: ex_alist
                                                                            └──Type expr: Variable: 2318
                                                                └──Desc: Variable
                                                                   └──Variable: bind
                                                                   └──Type expr: Constructor: ex_alist
                                                                      └──Type expr: Variable: 2318
                                                             └──Expression:
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: ex_alist
                                                                      └──Type expr: Variable: 2318
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ex_alist
                                                                            └──Type expr: Variable: 2318
                                                                         └──Type expr: Constructor: option
                                                                            └──Type expr: Constructor: ex_alist
                                                                               └──Type expr: Variable: 2318
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Variable: 2318
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: ex_alist
                                                                                     └──Type expr: Variable: 2318
                                                                                  └──Type expr: Constructor: option
                                                                                     └──Type expr: Constructor: ex_alist
                                                                                        └──Type expr: Variable: 2318
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: term
                                                                                        └──Type expr: Variable: 2318
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Variable: 2318
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Constructor: ex_alist
                                                                                              └──Type expr: Variable: 2318
                                                                                           └──Type expr: Constructor: option
                                                                                              └──Type expr: Constructor: ex_alist
                                                                                                 └──Type expr: Variable: 2318
                                                                                  └──Desc: Variable
                                                                                     └──Variable: amgu
                                                                                     └──Type expr: Variable: 2318
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: term
                                                                                     └──Type expr: Variable: 2318
                                                                                  └──Desc: Variable
                                                                                     └──Variable: s1
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 2318
                                                                            └──Desc: Variable
                                                                               └──Variable: t1
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ex_alist
                                                                         └──Type expr: Variable: 2318
                                                                      └──Desc: Variable
                                                                         └──Variable: acc
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: ex_alist
                                                                └──Type expr: Variable: 2318
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: 2318
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 2318
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: ex_alist
                                                                         └──Type expr: Variable: 2318
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: ex_alist
                                                                            └──Type expr: Variable: 2318
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: 2318
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 2318
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: ex_alist
                                                                                  └──Type expr: Variable: 2318
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: ex_alist
                                                                                     └──Type expr: Variable: 2318
                                                                      └──Desc: Variable
                                                                         └──Variable: amgu
                                                                         └──Type expr: Variable: 2318
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 2318
                                                                      └──Desc: Variable
                                                                         └──Variable: s2
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 2318
                                                                └──Desc: Variable
                                                                   └──Variable: t2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: term
                         └──Type expr: Variable: 2575
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 2575
                         └──Type expr: Constructor: option
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Variable: 2575
                   └──Desc: Variable: mgu
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 2575
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 2575
                            └──Type expr: Constructor: option
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Variable: 2575
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 2575
                            └──Desc: Variable: s
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 2575
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Variable: 2575
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 2575
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Constructor: ex_alist
                                        └──Type expr: Variable: 2575
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: ex_alist
                                              └──Type expr: Variable: 2575
                                           └──Type expr: Constructor: option
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Variable: 2575
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 2575
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: ex_alist
                                                       └──Type expr: Variable: 2575
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: 2575
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 2575
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 2575
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: ex_alist
                                                                └──Type expr: Variable: 2575
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: 2575
                                                    └──Desc: Variable
                                                       └──Variable: amgu
                                                       └──Type expr: Variable: 2575
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 2575
                                                    └──Desc: Variable
                                                       └──Variable: s
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 2575
                                              └──Desc: Variable
                                                 └──Variable: t
                                     └──Expression:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: 2575
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Exists_alist
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: 2575
                                                    └──Type expr: Variable: 2575
                                              └──Constructor type:
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Variable: 2575
                                           └──Expression:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: 2575
                                                 └──Type expr: Variable: 2575
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Anil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: 2575
                                                          └──Type expr: Variable: 2575 |}]
