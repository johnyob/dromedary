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
                   └──Constructor alphas: 7408
                   └──Constructor type:
                      └──Type expr: Constructor: nat
                         └──Type expr: Variable: 7408
                   └──Constraint:
                      └──Type expr: Variable: 7408
                      └──Type expr: Constructor: zero
                └──Constructor declaration:
                   └──Constructor name: Succ
                   └──Constructor alphas: 7408
                   └──Constructor type:
                      └──Type expr: Constructor: nat
                         └──Type expr: Variable: 7408
                   └──Constructor argument:
                      └──Constructor betas: 7411
                      └──Type expr: Constructor: nat
                         └──Type expr: Variable: 7411
                   └──Constraint:
                      └──Type expr: Variable: 7408
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: 7411
       └──Structure item: Type
          └──Type declaration:
             └──Type name: fin
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Fin_zero
                   └──Constructor alphas: 7415
                   └──Constructor type:
                      └──Type expr: Constructor: fin
                         └──Type expr: Variable: 7415
                   └──Constructor argument:
                      └──Constructor betas: 7416
                      └──Type expr: Constructor: unit
                   └──Constraint:
                      └──Type expr: Variable: 7415
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: 7416
                └──Constructor declaration:
                   └──Constructor name: Fin_succ
                   └──Constructor alphas: 7415
                   └──Constructor type:
                      └──Type expr: Constructor: fin
                         └──Type expr: Variable: 7415
                   └──Constructor argument:
                      └──Constructor betas: 7420
                      └──Type expr: Constructor: fin
                         └──Type expr: Variable: 7420
                   └──Constraint:
                      └──Type expr: Variable: 7415
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: 7420
       └──Structure item: Type
          └──Type declaration:
             └──Type name: is_succ
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Is_succ
                   └──Constructor alphas: 7424
                   └──Constructor type:
                      └──Type expr: Constructor: is_succ
                         └──Type expr: Variable: 7424
                   └──Constructor argument:
                      └──Constructor betas: 7425
                      └──Type expr: Constructor: unit
                   └──Constraint:
                      └──Type expr: Variable: 7424
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: 7425
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: fin
                         └──Type expr: Variable: 7464
                      └──Type expr: Constructor: is_succ
                         └──Type expr: Variable: 7464
                   └──Desc: Variable: fin_succ
                └──Abstraction:
                   └──Variables: 7464
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: 7464
                         └──Type expr: Constructor: is_succ
                            └──Type expr: Variable: 7464
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 7464
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Constructor: is_succ
                               └──Type expr: Variable: 7464
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: 7464
                                  └──Desc: Variable
                                     └──Variable: f
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 7464
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: 7464
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_zero
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 7464
                                           └──Pattern:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
                                     └──Expression:
                                        └──Type expr: Constructor: is_succ
                                           └──Type expr: Variable: 7464
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Is_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: is_succ
                                                    └──Type expr: Variable: 7464
                                           └──Expression:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: 7464
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 7505
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 7464
                                           └──Pattern:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: 7505
                                              └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Constructor: is_succ
                                           └──Type expr: Variable: 7464
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Is_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: is_succ
                                                    └──Type expr: Variable: 7464
                                           └──Expression:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
       └──Structure item: Type
          └──Type declaration:
             └──Type name: term
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Var
                   └──Constructor alphas: 7429
                   └──Constructor type:
                      └──Type expr: Constructor: term
                         └──Type expr: Variable: 7429
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: fin
                         └──Type expr: Variable: 7429
                └──Constructor declaration:
                   └──Constructor name: Leaf
                   └──Constructor alphas: 7429
                   └──Constructor type:
                      └──Type expr: Constructor: term
                         └──Type expr: Variable: 7429
                └──Constructor declaration:
                   └──Constructor name: Fork
                   └──Constructor alphas: 7429
                   └──Constructor type:
                      └──Type expr: Constructor: term
                         └──Type expr: Variable: 7429
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 7429
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 7429
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: fin
                         └──Type expr: Variable: 7534
                      └──Type expr: Constructor: term
                         └──Type expr: Variable: 7534
                   └──Desc: Variable: var
                └──Abstraction:
                   └──Variables: 7534
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: 7534
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 7534
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 7534
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 7534
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Var
                                  └──Constructor argument type:
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Variable: 7534
                                  └──Constructor type:
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: 7534
                               └──Expression:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: 7534
                                  └──Desc: Variable
                                     └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: 7540
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: 7562
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: 7540
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 7562
                   └──Desc: Variable: lift
                └──Abstraction:
                   └──Variables: 7562,7562,7540
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 7540
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 7562
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 7540
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 7562
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 7540
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 7562
                            └──Desc: Variable: r
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 7540
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 7562
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: 7540
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 7562
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Var
                                        └──Constructor argument type:
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: 7562
                                        └──Constructor type:
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: 7562
                                     └──Expression:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: 7562
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 7540
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 7562
                                              └──Desc: Variable
                                                 └──Variable: r
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: 7540
                                              └──Desc: Variable
                                                 └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: pre_subst
                └──Abstraction:
                   └──Variables: 7608
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 7595
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 7608
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 7595
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 7608
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 7595
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 7608
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 7595
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 7608
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 7595
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 7608
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: 7595
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: 7595
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 7595
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 7595
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 7595
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 7595
                                                    └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 7608
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 7595
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 7608
                                                    └──Desc: Variable
                                                       └──Variable: f
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 7595
                                                    └──Desc: Variable
                                                       └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 7595
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Leaf
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 7595
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 7608
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Leaf
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 7608
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 7595
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fork
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 7595
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 7595
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 7595
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 7595
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 7595
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 7595
                                                          └──Desc: Variable: t1
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 7595
                                                          └──Desc: Variable: t2
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 7608
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fork
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 7608
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 7608
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 7608
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 7608
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 7608
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 7608
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 7595
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 7608
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: 7595
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 7608
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 7595
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 7608
                                                                      └──Desc: Variable
                                                                         └──Variable: pre_subst
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: 7595
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: 7608
                                                                      └──Desc: Variable
                                                                         └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 7595
                                                                └──Desc: Variable
                                                                   └──Variable: t1
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 7608
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 7595
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 7608
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: 7595
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 7608
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 7595
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 7608
                                                                      └──Desc: Variable
                                                                         └──Variable: pre_subst
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: 7595
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: 7608
                                                                      └──Desc: Variable
                                                                         └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 7595
                                                                └──Desc: Variable
                                                                   └──Variable: t2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: 7662
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 7664
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 7636
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 7662
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 7636
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 7664
                   └──Desc: Variable: comp_subst
                └──Abstraction:
                   └──Variables: 7636
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 7662
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 7664
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 7636
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 7662
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 7636
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 7664
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 7662
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 7664
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: 7636
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 7662
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: 7636
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 7664
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Variable: 7636
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: 7662
                                  └──Desc: Variable: g
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Variable: 7636
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: 7664
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: 7636
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: 7664
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 7662
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 7664
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 7662
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 7664
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 7662
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 7664
                                                    └──Desc: Variable
                                                       └──Variable: pre_subst
                                                       └──Type expr: Variable: 7664
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 7662
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 7664
                                                    └──Desc: Variable
                                                       └──Variable: f
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 7662
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 7636
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 7662
                                                    └──Desc: Variable
                                                       └──Variable: g
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 7636
                                                    └──Desc: Variable
                                                       └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: thin
                └──Abstraction:
                   └──Variables: 7686
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 7718
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 7718
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 7718
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 7718
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 7718
                               └──Type expr: Constructor: fin
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: 7718
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: 7718
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: 7718
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Variable: 7718
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: 7718
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 7718
                                              └──Desc: Variable
                                                 └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: 7718
                                              └──Desc: Variable
                                                 └──Variable: y
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 7718
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: 7718
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 7718
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 7718
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 7718
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 7718
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 7718
                                                    └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 7718
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fin_succ
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 7718
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 7718
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 7718
                                                    └──Desc: Variable
                                                       └──Variable: y
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 7718
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 7718
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 7718
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 7790
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 7718
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 7790
                                                          └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 7718
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 7718
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 7718
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fin_zero
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: unit
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 7718
                                                 └──Expression:
                                                    └──Type expr: Constructor: unit
                                                    └──Desc: Constant: ()
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 7718
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 7718
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 7718
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 7830
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 7718
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 7830
                                                          └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 7718
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 7827
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 7718
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 7827
                                                          └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 7718
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fin_succ
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 7718
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 7718
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 7718
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 7827
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 7718
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: 7830
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: 7827
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: 7718
                                                                └──Desc: Variable
                                                                   └──Variable: thin
                                                                   └──Type expr: Variable: 7827
                                                             └──Expression:
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: 7830
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 7827
                                                          └──Desc: Variable
                                                             └──Variable: y
       └──Structure item: Type
          └──Type declaration:
             └──Type name: option
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: None
                   └──Constructor alphas: 7437
                   └──Constructor type:
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: 7437
                └──Constructor declaration:
                   └──Constructor name: Some
                   └──Constructor alphas: 7437
                   └──Constructor type:
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: 7437
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: 7437
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: 7899
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: 7899
                            └──Type expr: Constructor: option
                               └──Type expr: Variable: 7893
                         └──Type expr: Constructor: option
                            └──Type expr: Variable: 7893
                   └──Desc: Variable: bind
                └──Abstraction:
                   └──Variables: 7899,7899,7899
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: option
                            └──Type expr: Variable: 7899
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: 7899
                               └──Type expr: Constructor: option
                                  └──Type expr: Variable: 7893
                            └──Type expr: Constructor: option
                               └──Type expr: Variable: 7893
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: option
                               └──Type expr: Variable: 7899
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 7899
                                  └──Type expr: Constructor: option
                                     └──Type expr: Variable: 7893
                               └──Type expr: Constructor: option
                                  └──Type expr: Variable: 7893
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 7899
                                     └──Type expr: Constructor: option
                                        └──Type expr: Variable: 7893
                                  └──Desc: Variable: f
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Variable: 7893
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: option
                                           └──Type expr: Variable: 7899
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Constructor: option
                                        └──Type expr: Variable: 7899
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Variable: 7899
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: None
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Variable: 7899
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Variable: 7893
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: None
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Variable: 7893
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Variable: 7899
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Some
                                                    └──Constructor argument type:
                                                       └──Type expr: Variable: 7899
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Variable: 7899
                                                 └──Pattern:
                                                    └──Type expr: Variable: 7899
                                                    └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Variable: 7893
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 7899
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Variable: 7893
                                                    └──Desc: Variable
                                                       └──Variable: f
                                                 └──Expression:
                                                    └──Type expr: Variable: 7899
                                                    └──Desc: Variable
                                                       └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: thick
                └──Abstraction:
                   └──Variables: 7919
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 7953
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 7953
                            └──Type expr: Constructor: option
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 7953
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 7953
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: 7953
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: 7953
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: 7953
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Variable: 7953
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Variable: 7953
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Variable: 7953
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 7953
                                              └──Desc: Variable
                                                 └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 7953
                                              └──Desc: Variable
                                                 └──Variable: y
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 7953
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 7953
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 7953
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 7953
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 7953
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 7953
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 7953
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 7953
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 7953
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: None
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 7953
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 7953
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 7953
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 7953
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 7953
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 7953
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 8031
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 7953
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 8031
                                                          └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 7953
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Some
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 7953
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 7953
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 7953
                                                    └──Desc: Variable
                                                       └──Variable: y
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 7953
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 7953
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 7953
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 8069
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 7953
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 8069
                                                          └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 7953
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 7953
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 7953
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Constructor: is_succ
                                                       └──Type expr: Variable: 8069
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 8069
                                                             └──Type expr: Constructor: is_succ
                                                                └──Type expr: Variable: 8069
                                                          └──Desc: Variable
                                                             └──Variable: fin_succ
                                                             └──Type expr: Variable: 8069
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 8069
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Type expr: Constructor: is_succ
                                                    └──Type expr: Variable: 8069
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Constructor: is_succ
                                                             └──Type expr: Variable: 8069
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Is_succ
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: unit
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: is_succ
                                                                      └──Type expr: Variable: 8069
                                                             └──Pattern:
                                                                └──Type expr: Constructor: unit
                                                                └──Desc: Constant: ()
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 7953
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Some
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: 7953
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: 7953
                                                             └──Expression:
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: 7953
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Fin_zero
                                                                      └──Constructor argument type:
                                                                         └──Type expr: Constructor: unit
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: 7953
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: unit
                                                                      └──Desc: Constant: ()
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 7953
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 7953
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 7953
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 8147
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 7953
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 8147
                                                          └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 7953
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 8144
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 7953
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 8144
                                                          └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 7953
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Constructor: is_succ
                                                       └──Type expr: Variable: 8147
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 8147
                                                             └──Type expr: Constructor: is_succ
                                                                └──Type expr: Variable: 8147
                                                          └──Desc: Variable
                                                             └──Variable: fin_succ
                                                             └──Type expr: Variable: 8147
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 8147
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Type expr: Constructor: is_succ
                                                    └──Type expr: Variable: 8147
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Constructor: is_succ
                                                             └──Type expr: Variable: 8147
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Is_succ
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: unit
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: is_succ
                                                                      └──Type expr: Variable: 8147
                                                             └──Pattern:
                                                                └──Type expr: Constructor: unit
                                                                └──Desc: Constant: ()
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 7953
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: 8248
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: 7953
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: 7953
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: option
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: 8248
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Variable: 8248
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Variable: 7953
                                                                            └──Type expr: Constructor: option
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Variable: 7953
                                                                      └──Desc: Variable
                                                                         └──Variable: bind
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: 8248
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: 8248
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Variable: 8144
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Variable: 8248
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: fin
                                                                                        └──Type expr: Variable: 8147
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: fin
                                                                                           └──Type expr: Variable: 8144
                                                                                        └──Type expr: Constructor: option
                                                                                           └──Type expr: Constructor: fin
                                                                                              └──Type expr: Variable: 8248
                                                                                  └──Desc: Variable
                                                                                     └──Variable: thick
                                                                                     └──Type expr: Variable: 8248
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Variable: 8147
                                                                                  └──Desc: Variable
                                                                                     └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: 8144
                                                                            └──Desc: Variable
                                                                               └──Variable: y
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: 8248
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: 7953
                                                                └──Desc: Function
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: 8248
                                                                      └──Desc: Variable: x
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: 7953
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Some
                                                                            └──Constructor argument type:
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Variable: 7953
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Variable: 7953
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: 7953
                                                                            └──Desc: Construct
                                                                               └──Constructor description:
                                                                                  └──Name: Fin_succ
                                                                                  └──Constructor argument type:
                                                                                     └──Type expr: Constructor: fin
                                                                                        └──Type expr: Variable: 8248
                                                                                  └──Constructor type:
                                                                                     └──Type expr: Constructor: fin
                                                                                        └──Type expr: Variable: 7953
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Variable: 8248
                                                                                  └──Desc: Variable
                                                                                     └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: check
                └──Abstraction:
                   └──Variables: 8272
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 8306
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 8306
                            └──Type expr: Constructor: option
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 8306
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 8306
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: 8306
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 8306
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: 8306
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: 8306
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: term
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 8306
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Constructor: term
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: 8306
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 8306
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 8306
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 8306
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 8306
                                                    └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 8306
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 8306
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 8306
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 8306
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: 8306
                                                             └──Type expr: Arrow
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: 8306
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 8306
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 8306
                                                          └──Desc: Variable
                                                             └──Variable: bind
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 8306
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 8306
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Constructor: succ
                                                                         └──Type expr: Variable: 8306
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: 8306
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Constructor: succ
                                                                               └──Type expr: Variable: 8306
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Constructor: succ
                                                                                  └──Type expr: Variable: 8306
                                                                            └──Type expr: Constructor: option
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Variable: 8306
                                                                      └──Desc: Variable
                                                                         └──Variable: thick
                                                                         └──Type expr: Variable: 8306
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: 8306
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: 8306
                                                                └──Desc: Variable
                                                                   └──Variable: y
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 8306
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 8306
                                                    └──Desc: Function
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 8306
                                                          └──Desc: Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 8306
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Some
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 8306
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 8306
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 8306
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Var
                                                                      └──Constructor argument type:
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: 8306
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: 8306
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: 8306
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 8306
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Leaf
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 8306
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 8306
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Some
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 8306
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 8306
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 8306
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Leaf
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 8306
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 8306
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fork
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 8306
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 8306
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 8306
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 8306
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 8306
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 8306
                                                          └──Desc: Variable: t1
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 8306
                                                          └──Desc: Variable: t2
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 8306
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 8306
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 8306
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 8306
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 8306
                                                             └──Type expr: Arrow
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 8306
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 8306
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 8306
                                                          └──Desc: Variable
                                                             └──Variable: bind
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 8306
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 8306
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Constructor: succ
                                                                         └──Type expr: Variable: 8306
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 8306
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Constructor: succ
                                                                               └──Type expr: Variable: 8306
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Constructor: succ
                                                                                  └──Type expr: Variable: 8306
                                                                            └──Type expr: Constructor: option
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Variable: 8306
                                                                      └──Desc: Variable
                                                                         └──Variable: check
                                                                         └──Type expr: Variable: 8306
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: 8306
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: 8306
                                                                └──Desc: Variable
                                                                   └──Variable: t1
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 8306
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 8306
                                                    └──Desc: Function
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 8306
                                                          └──Desc: Variable: t1
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 8306
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 8306
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: 8306
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 8306
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: option
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 8306
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Variable: 8306
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: term
                                                                                     └──Type expr: Variable: 8306
                                                                            └──Type expr: Constructor: option
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Variable: 8306
                                                                      └──Desc: Variable
                                                                         └──Variable: bind
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: 8306
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: 8306
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Constructor: succ
                                                                                     └──Type expr: Variable: 8306
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: term
                                                                                     └──Type expr: Variable: 8306
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: fin
                                                                                        └──Type expr: Constructor: succ
                                                                                           └──Type expr: Variable: 8306
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Constructor: succ
                                                                                              └──Type expr: Variable: 8306
                                                                                        └──Type expr: Constructor: option
                                                                                           └──Type expr: Constructor: term
                                                                                              └──Type expr: Variable: 8306
                                                                                  └──Desc: Variable
                                                                                     └──Variable: check
                                                                                     └──Type expr: Variable: 8306
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Constructor: succ
                                                                                        └──Type expr: Variable: 8306
                                                                                  └──Desc: Variable
                                                                                     └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Constructor: succ
                                                                                  └──Type expr: Variable: 8306
                                                                            └──Desc: Variable
                                                                               └──Variable: t2
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 8306
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 8306
                                                                └──Desc: Function
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 8306
                                                                      └──Desc: Variable: t2
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: 8306
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Some
                                                                            └──Constructor argument type:
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Variable: 8306
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: term
                                                                                     └──Type expr: Variable: 8306
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 8306
                                                                            └──Desc: Construct
                                                                               └──Constructor description:
                                                                                  └──Name: Fork
                                                                                  └──Constructor argument type:
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Variable: 8306
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Variable: 8306
                                                                                  └──Constructor type:
                                                                                     └──Type expr: Constructor: term
                                                                                        └──Type expr: Variable: 8306
                                                                               └──Expression:
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Constructor: term
                                                                                        └──Type expr: Variable: 8306
                                                                                     └──Type expr: Constructor: term
                                                                                        └──Type expr: Variable: 8306
                                                                                  └──Desc: Tuple
                                                                                     └──Expression:
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Variable: 8306
                                                                                        └──Desc: Variable
                                                                                           └──Variable: t1
                                                                                     └──Expression:
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Variable: 8306
                                                                                        └──Desc: Variable
                                                                                           └──Variable: t2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: fin
                         └──Type expr: Constructor: succ
                            └──Type expr: Variable: 8561
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 8561
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 8561
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 8561
                   └──Desc: Variable: subst_var
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 8561
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 8561
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: 8561
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 8561
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 8561
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 8561
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: 8561
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 8561
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 8561
                                  └──Desc: Variable: t'
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: 8561
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: 8561
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 8561
                                        └──Desc: Variable: y
                                     └──Expression:
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: 8561
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 8561
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 8561
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 8561
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 8561
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: 8561
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: 8561
                                                          └──Desc: Variable
                                                             └──Variable: thick
                                                             └──Type expr: Variable: 8561
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 8561
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 8561
                                                    └──Desc: Variable
                                                       └──Variable: y
                                           └──Type expr: Constructor: option
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: 8561
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 8561
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: None
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: 8561
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 8561
                                                    └──Desc: Variable
                                                       └──Variable: t'
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 8561
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Some
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 8561
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: 8561
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 8561
                                                          └──Desc: Variable: y'
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 8561
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Var
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 8561
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 8561
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 8561
                                                          └──Desc: Variable
                                                             └──Variable: y'
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: fin
                         └──Type expr: Constructor: succ
                            └──Type expr: Variable: 8583
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 8583
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 8583
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 8583
                   └──Desc: Variable: subst
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 8583
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 8583
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: 8583
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 8583
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 8583
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 8583
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: term
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: 8583
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 8583
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 8583
                                  └──Desc: Variable: t'
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: term
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: 8583
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: 8583
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 8583
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 8583
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 8583
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 8583
                                        └──Desc: Variable
                                           └──Variable: pre_subst
                                           └──Type expr: Variable: 8583
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Variable: 8583
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: 8583
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 8583
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 8583
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 8583
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 8583
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 8583
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 8583
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 8583
                                                    └──Desc: Variable
                                                       └──Variable: subst_var
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 8583
                                                    └──Desc: Variable
                                                       └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 8583
                                              └──Desc: Variable
                                                 └──Variable: t'
       └──Structure item: Type
          └──Type declaration:
             └──Type name: alist
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Anil
                   └──Constructor alphas: 7440 7441
                   └──Constructor type:
                      └──Type expr: Constructor: alist
                         └──Type expr: Variable: 7440
                         └──Type expr: Variable: 7441
                   └──Constraint:
                      └──Type expr: Variable: 7440
                      └──Type expr: Variable: 7441
                └──Constructor declaration:
                   └──Constructor name: Asnoc
                   └──Constructor alphas: 7440 7441
                   └──Constructor type:
                      └──Type expr: Constructor: alist
                         └──Type expr: Variable: 7440
                         └──Type expr: Variable: 7441
                   └──Constructor argument:
                      └──Constructor betas: 7443
                      └──Type expr: Tuple
                         └──Type expr: Constructor: alist
                            └──Type expr: Variable: 7443
                            └──Type expr: Variable: 7441
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 7443
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 7443
                   └──Constraint:
                      └──Type expr: Variable: 7440
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: 7443
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: sub
                └──Abstraction:
                   └──Variables: 8613,8612
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: alist
                            └──Type expr: Variable: 8640
                            └──Type expr: Variable: 8641
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 8640
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 8641
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: 8640
                               └──Type expr: Variable: 8641
                            └──Desc: Variable: s
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 8640
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 8641
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: alist
                                     └──Type expr: Variable: 8640
                                     └──Type expr: Variable: 8641
                                  └──Desc: Variable
                                     └──Variable: s
                               └──Type expr: Constructor: alist
                                  └──Type expr: Variable: 8640
                                  └──Type expr: Variable: 8641
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Variable: 8640
                                           └──Type expr: Variable: 8641
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Anil
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: 8640
                                                    └──Type expr: Variable: 8641
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: 8640
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: 8641
                                        └──Desc: Variable
                                           └──Variable: var
                                           └──Type expr: Variable: 8640
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Variable: 8640
                                           └──Type expr: Variable: 8641
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Asnoc
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: 8706
                                                       └──Type expr: Variable: 8641
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 8706
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 8706
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: 8640
                                                    └──Type expr: Variable: 8641
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: 8706
                                                    └──Type expr: Variable: 8641
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 8706
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 8706
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: 8706
                                                       └──Type expr: Variable: 8641
                                                    └──Desc: Variable: s
                                                 └──Pattern:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 8706
                                                    └──Desc: Variable: t
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 8706
                                                    └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: 8640
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: 8641
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 8640
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 8706
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 8640
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 8641
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 8706
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 8641
                                                       └──Type expr: Arrow
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 8640
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 8706
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 8640
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 8641
                                                    └──Desc: Variable
                                                       └──Variable: comp_subst
                                                       └──Type expr: Variable: 8640
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 8706
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 8641
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: alist
                                                                └──Type expr: Variable: 8706
                                                                └──Type expr: Variable: 8641
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: 8706
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 8641
                                                          └──Desc: Variable
                                                             └──Variable: sub
                                                             └──Type expr: Variable: 8641
                                                             └──Type expr: Variable: 8706
                                                       └──Expression:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: 8706
                                                             └──Type expr: Variable: 8641
                                                          └──Desc: Variable
                                                             └──Variable: s
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 8640
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 8706
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 8706
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 8640
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 8706
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 8706
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 8706
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: 8640
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 8706
                                                          └──Desc: Variable
                                                             └──Variable: subst_var
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 8706
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 8706
                                                    └──Desc: Variable
                                                       └──Variable: t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: append
                └──Abstraction:
                   └──Variables: 8794,8798,8797
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: alist
                            └──Type expr: Variable: 8828
                            └──Type expr: Variable: 8829
                         └──Type expr: Arrow
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: 8840
                               └──Type expr: Variable: 8828
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: 8840
                               └──Type expr: Variable: 8829
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: 8828
                               └──Type expr: Variable: 8829
                            └──Desc: Variable: s1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: alist
                                  └──Type expr: Variable: 8840
                                  └──Type expr: Variable: 8828
                               └──Type expr: Constructor: alist
                                  └──Type expr: Variable: 8840
                                  └──Type expr: Variable: 8829
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: alist
                                     └──Type expr: Variable: 8840
                                     └──Type expr: Variable: 8828
                                  └──Desc: Variable: s2
                               └──Expression:
                                  └──Type expr: Constructor: alist
                                     └──Type expr: Variable: 8840
                                     └──Type expr: Variable: 8829
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Variable: 8840
                                           └──Type expr: Variable: 8828
                                        └──Desc: Variable
                                           └──Variable: s2
                                     └──Type expr: Constructor: alist
                                        └──Type expr: Variable: 8840
                                        └──Type expr: Variable: 8828
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: 8840
                                                 └──Type expr: Variable: 8828
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Anil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: 8840
                                                          └──Type expr: Variable: 8828
                                           └──Expression:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: 8840
                                                 └──Type expr: Variable: 8829
                                              └──Desc: Variable
                                                 └──Variable: s1
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: 8840
                                                 └──Type expr: Variable: 8828
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Asnoc
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: 8889
                                                             └──Type expr: Variable: 8828
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 8889
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 8889
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: 8840
                                                          └──Type expr: Variable: 8828
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: 8889
                                                          └──Type expr: Variable: 8828
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 8889
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 8889
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: 8889
                                                             └──Type expr: Variable: 8828
                                                          └──Desc: Variable: s2
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 8889
                                                          └──Desc: Variable: t
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 8889
                                                          └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: 8840
                                                 └──Type expr: Variable: 8829
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Asnoc
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: 8889
                                                             └──Type expr: Variable: 8829
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 8889
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 8889
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: 8840
                                                          └──Type expr: Variable: 8829
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: 8889
                                                          └──Type expr: Variable: 8829
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 8889
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 8889
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: 8889
                                                             └──Type expr: Variable: 8829
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: alist
                                                                      └──Type expr: Variable: 8889
                                                                      └──Type expr: Variable: 8828
                                                                   └──Type expr: Constructor: alist
                                                                      └──Type expr: Variable: 8889
                                                                      └──Type expr: Variable: 8829
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: alist
                                                                            └──Type expr: Variable: 8828
                                                                            └──Type expr: Variable: 8829
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: alist
                                                                               └──Type expr: Variable: 8889
                                                                               └──Type expr: Variable: 8828
                                                                            └──Type expr: Constructor: alist
                                                                               └──Type expr: Variable: 8889
                                                                               └──Type expr: Variable: 8829
                                                                      └──Desc: Variable
                                                                         └──Variable: append
                                                                         └──Type expr: Variable: 8889
                                                                         └──Type expr: Variable: 8829
                                                                         └──Type expr: Variable: 8828
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: alist
                                                                         └──Type expr: Variable: 8828
                                                                         └──Type expr: Variable: 8829
                                                                      └──Desc: Variable
                                                                         └──Variable: s1
                                                             └──Expression:
                                                                └──Type expr: Constructor: alist
                                                                   └──Type expr: Variable: 8889
                                                                   └──Type expr: Variable: 8828
                                                                └──Desc: Variable
                                                                   └──Variable: s2
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 8889
                                                          └──Desc: Variable
                                                             └──Variable: t
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 8889
                                                          └──Desc: Variable
                                                             └──Variable: x
       └──Structure item: Type
          └──Type declaration:
             └──Type name: ex_alist
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Exists_alist
                   └──Constructor alphas: 7451
                   └──Constructor type:
                      └──Type expr: Constructor: ex_alist
                         └──Type expr: Variable: 7451
                   └──Constructor argument:
                      └──Constructor betas: 7452
                      └──Type expr: Constructor: alist
                         └──Type expr: Variable: 7451
                         └──Type expr: Variable: 7452
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: alist
                         └──Type expr: Variable: 8976
                         └──Type expr: Variable: 8975
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 8976
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 8976
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 8976
                   └──Desc: Variable: asnoc
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: alist
                            └──Type expr: Variable: 8976
                            └──Type expr: Variable: 8975
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 8976
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: 8976
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: 8976
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: 8976
                               └──Type expr: Variable: 8975
                            └──Desc: Variable: a
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 8976
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: 8976
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: 8976
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 8976
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: 8976
                                     └──Type expr: Constructor: ex_alist
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: 8976
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 8976
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 8976
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Exists_alist
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 8976
                                                    └──Type expr: Variable: 8975
                                              └──Constructor type:
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 8976
                                           └──Expression:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 8976
                                                 └──Type expr: Variable: 8975
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Asnoc
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: 8976
                                                             └──Type expr: Variable: 8975
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 8976
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 8976
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 8976
                                                          └──Type expr: Variable: 8975
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: 8976
                                                          └──Type expr: Variable: 8975
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 8976
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 8976
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: 8976
                                                             └──Type expr: Variable: 8975
                                                          └──Desc: Variable
                                                             └──Variable: a
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 8976
                                                          └──Desc: Variable
                                                             └──Variable: t
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 8976
                                                          └──Desc: Variable
                                                             └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: weaken_fin
                └──Abstraction:
                   └──Variables: 9004
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: 9025
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 9025
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 9025
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 9025
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: 9025
                                  └──Desc: Variable
                                     └──Variable: f
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 9025
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: 9025
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_zero
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 9025
                                           └──Pattern:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
                                     └──Expression:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 9025
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_zero
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 9025
                                           └──Expression:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: 9025
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 9071
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 9025
                                           └──Pattern:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: 9071
                                              └──Desc: Variable: f
                                     └──Expression:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 9025
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 9025
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 9025
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: 9025
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 9071
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 9025
                                                    └──Desc: Variable
                                                       └──Variable: weaken_fin
                                                       └──Type expr: Variable: 9071
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 9071
                                                    └──Desc: Variable
                                                       └──Variable: f
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: term
                         └──Type expr: Variable: 9140
                      └──Type expr: Constructor: term
                         └──Type expr: Constructor: succ
                            └──Type expr: Variable: 9140
                   └──Desc: Variable: weaken_term
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 9140
                         └──Type expr: Constructor: term
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 9140
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 9140
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: term
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 9140
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: 9140
                                     └──Type expr: Constructor: term
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: 9140
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: 9140
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 9140
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 9140
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 9140
                                        └──Desc: Variable
                                           └──Variable: pre_subst
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 9140
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: 9140
                                           └──Type expr: Constructor: term
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Variable: 9140
                                        └──Desc: Function
                                           └──Pattern:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: 9140
                                              └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 9140
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 9140
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 9140
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 9140
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 9140
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 9140
                                                          └──Desc: Variable
                                                             └──Variable: weaken_fin
                                                             └──Type expr: Variable: 9140
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 9140
                                                          └──Desc: Variable
                                                             └──Variable: x
                               └──Expression:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 9140
                                  └──Desc: Variable
                                     └──Variable: t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: weaken_alist
                └──Abstraction:
                   └──Variables: 9155,9154
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: alist
                            └──Type expr: Variable: 9182
                            └──Type expr: Variable: 9183
                         └──Type expr: Constructor: alist
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 9182
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 9183
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: 9182
                               └──Type expr: Variable: 9183
                            └──Desc: Variable: s
                         └──Expression:
                            └──Type expr: Constructor: alist
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 9182
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 9183
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: alist
                                     └──Type expr: Variable: 9182
                                     └──Type expr: Variable: 9183
                                  └──Desc: Variable
                                     └──Variable: s
                               └──Type expr: Constructor: alist
                                  └──Type expr: Variable: 9182
                                  └──Type expr: Variable: 9183
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Variable: 9182
                                           └──Type expr: Variable: 9183
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Anil
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: 9182
                                                    └──Type expr: Variable: 9183
                                     └──Expression:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 9182
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 9183
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Anil
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 9182
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 9182
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Variable: 9182
                                           └──Type expr: Variable: 9183
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Asnoc
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: 9248
                                                       └──Type expr: Variable: 9183
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 9248
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 9248
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: 9182
                                                    └──Type expr: Variable: 9183
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: 9248
                                                    └──Type expr: Variable: 9183
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 9248
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 9248
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: 9248
                                                       └──Type expr: Variable: 9183
                                                    └──Desc: Variable: s
                                                 └──Pattern:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 9248
                                                    └──Desc: Variable: t
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 9248
                                                    └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 9182
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: 9183
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Asnoc
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: 9182
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 9183
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 9182
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 9182
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 9182
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 9183
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: 9182
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 9183
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 9182
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 9182
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: 9182
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 9183
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: alist
                                                                └──Type expr: Variable: 9248
                                                                └──Type expr: Variable: 9183
                                                             └──Type expr: Constructor: alist
                                                                └──Type expr: Variable: 9182
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 9183
                                                          └──Desc: Variable
                                                             └──Variable: weaken_alist
                                                             └──Type expr: Variable: 9183
                                                             └──Type expr: Variable: 9248
                                                       └──Expression:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: 9248
                                                             └──Type expr: Variable: 9183
                                                          └──Desc: Variable
                                                             └──Variable: s
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 9182
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 9248
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 9182
                                                          └──Desc: Variable
                                                             └──Variable: weaken_term
                                                             └──Type expr: Variable: 9248
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 9248
                                                          └──Desc: Variable
                                                             └──Variable: t
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 9182
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 9182
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 9182
                                                          └──Desc: Variable
                                                             └──Variable: weaken_fin
                                                             └──Type expr: Variable: 9182
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 9182
                                                          └──Desc: Variable
                                                             └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: sub'
                └──Abstraction:
                   └──Variables: 9347
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ex_alist
                            └──Type expr: Variable: 9371
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: 9371
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 9371
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Variable: 9371
                            └──Desc: Variable: e
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: 9371
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 9371
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Variable: 9371
                                  └──Desc: Variable
                                     └──Variable: e
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Variable: 9371
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: 9371
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Exists_alist
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: 9371
                                                    └──Type expr: Variable: 9396
                                              └──Constructor type:
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Variable: 9371
                                           └──Pattern:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: 9371
                                                 └──Type expr: Variable: 9396
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Anil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: 9371
                                                          └──Type expr: Variable: 9396
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: 9371
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: 9371
                                        └──Desc: Variable
                                           └──Variable: var
                                           └──Type expr: Variable: 9371
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: 9371
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Exists_alist
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: 9371
                                                    └──Type expr: Variable: 9427
                                              └──Constructor type:
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Variable: 9371
                                           └──Pattern:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: 9371
                                                 └──Type expr: Variable: 9427
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Asnoc
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: 9446
                                                             └──Type expr: Variable: 9427
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 9446
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 9446
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: 9371
                                                          └──Type expr: Variable: 9427
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: 9446
                                                          └──Type expr: Variable: 9427
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 9446
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 9446
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: 9446
                                                             └──Type expr: Variable: 9427
                                                          └──Desc: Variable: s
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 9446
                                                          └──Desc: Variable: t
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 9446
                                                          └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: 9371
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: 9371
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 9371
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 9371
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 9371
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 9371
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 9371
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 9371
                                                       └──Type expr: Arrow
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 9371
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 9371
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 9371
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 9371
                                                    └──Desc: Variable
                                                       └──Variable: comp_subst
                                                       └──Type expr: Variable: 9371
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 9371
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 9371
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: ex_alist
                                                                └──Type expr: Variable: 9371
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: 9371
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 9371
                                                          └──Desc: Variable
                                                             └──Variable: sub'
                                                             └──Type expr: Variable: 9371
                                                       └──Expression:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: 9371
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Exists_alist
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: alist
                                                                      └──Type expr: Variable: 9371
                                                                      └──Type expr: Constructor: succ
                                                                         └──Type expr: Variable: 9427
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: ex_alist
                                                                      └──Type expr: Variable: 9371
                                                             └──Expression:
                                                                └──Type expr: Constructor: alist
                                                                   └──Type expr: Variable: 9371
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: 9427
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: alist
                                                                            └──Type expr: Variable: 9446
                                                                            └──Type expr: Variable: 9427
                                                                         └──Type expr: Constructor: alist
                                                                            └──Type expr: Variable: 9371
                                                                            └──Type expr: Constructor: succ
                                                                               └──Type expr: Variable: 9427
                                                                      └──Desc: Variable
                                                                         └──Variable: weaken_alist
                                                                         └──Type expr: Variable: 9427
                                                                         └──Type expr: Variable: 9446
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: alist
                                                                         └──Type expr: Variable: 9446
                                                                         └──Type expr: Variable: 9427
                                                                      └──Desc: Variable
                                                                         └──Variable: s
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 9371
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 9371
                                              └──Desc: Function
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 9371
                                                    └──Desc: Variable: t'
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 9371
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 9446
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 9371
                                                          └──Desc: Variable
                                                             └──Variable: weaken_term
                                                             └──Type expr: Variable: 9446
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 9446
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: 9371
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 9446
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: 9446
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: 9371
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 9446
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Constructor: succ
                                                                                     └──Type expr: Variable: 9446
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: term
                                                                                     └──Type expr: Variable: 9446
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: fin
                                                                                        └──Type expr: Variable: 9371
                                                                                     └──Type expr: Constructor: term
                                                                                        └──Type expr: Variable: 9446
                                                                            └──Desc: Variable
                                                                               └──Variable: subst_var
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Constructor: succ
                                                                                  └──Type expr: Variable: 9446
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 9446
                                                                      └──Desc: Variable
                                                                         └──Variable: t
                                                             └──Expression:
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: 9371
                                                                └──Desc: Variable
                                                                   └──Variable: t'
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: ex_alist
                         └──Type expr: Variable: 9574
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 9574
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 9574
                   └──Desc: Variable: subst'
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ex_alist
                            └──Type expr: Variable: 9574
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 9574
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 9574
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Variable: 9574
                            └──Desc: Variable: e
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 9574
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 9574
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Arrow
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: 9574
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: 9574
                                     └──Type expr: Arrow
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: 9574
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: 9574
                                  └──Desc: Variable
                                     └──Variable: pre_subst
                                     └──Type expr: Variable: 9574
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Variable: 9574
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: 9574
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: ex_alist
                                              └──Type expr: Variable: 9574
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: 9574
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 9574
                                        └──Desc: Variable
                                           └──Variable: sub'
                                           └──Type expr: Variable: 9574
                                     └──Expression:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: 9574
                                        └──Desc: Variable
                                           └──Variable: e
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: fin
                         └──Type expr: Constructor: succ
                            └──Type expr: Variable: 9638
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 9638
                         └──Type expr: Constructor: ex_alist
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 9638
                   └──Desc: Variable: flex_flex
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 9638
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 9638
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 9638
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 9638
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: 9638
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: 9638
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: 9638
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: 9638
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: option
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: 9638
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 9638
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 9638
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 9638
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 9638
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: 9638
                                                    └──Desc: Variable
                                                       └──Variable: thick
                                                       └──Type expr: Variable: 9638
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 9638
                                                    └──Desc: Variable
                                                       └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 9638
                                              └──Desc: Variable
                                                 └──Variable: y
                                     └──Type expr: Constructor: option
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: 9638
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 9638
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Some
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: 9638
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 9638
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: 9638
                                                    └──Desc: Variable: y'
                                           └──Expression:
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 9638
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 9638
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 9638
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: 9638
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: 9638
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: 9638
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: alist
                                                                      └──Type expr: Variable: 9638
                                                                      └──Type expr: Variable: 9638
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 9638
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Constructor: succ
                                                                               └──Type expr: Variable: 9638
                                                                         └──Type expr: Constructor: ex_alist
                                                                            └──Type expr: Constructor: succ
                                                                               └──Type expr: Variable: 9638
                                                                └──Desc: Variable
                                                                   └──Variable: asnoc
                                                                   └──Type expr: Variable: 9638
                                                                   └──Type expr: Variable: 9638
                                                             └──Expression:
                                                                └──Type expr: Constructor: alist
                                                                   └──Type expr: Variable: 9638
                                                                   └──Type expr: Variable: 9638
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Anil
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: alist
                                                                            └──Type expr: Variable: 9638
                                                                            └──Type expr: Variable: 9638
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 9638
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Var
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: 9638
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 9638
                                                             └──Expression:
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: 9638
                                                                └──Desc: Variable
                                                                   └──Variable: y'
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 9638
                                                    └──Desc: Variable
                                                       └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: 9638
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: None
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: 9638
                                           └──Expression:
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 9638
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Exists_alist
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 9638
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 9638
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 9638
                                                 └──Expression:
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 9638
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 9638
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Anil
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: alist
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 9638
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 9638
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: fin
                         └──Type expr: Constructor: succ
                            └──Type expr: Variable: 9720
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 9720
                         └──Type expr: Constructor: option
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 9720
                   └──Desc: Variable: flex_rigid
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: 9720
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 9720
                            └──Type expr: Constructor: option
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: 9720
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: 9720
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: 9720
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: 9720
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: 9720
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Constructor: ex_alist
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: 9720
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 9720
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 9720
                                           └──Type expr: Constructor: option
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 9720
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 9720
                                                 └──Type expr: Arrow
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 9720
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 9720
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 9720
                                              └──Desc: Variable
                                                 └──Variable: bind
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 9720
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 9720
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 9720
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 9720
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 9720
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: 9720
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 9720
                                                          └──Desc: Variable
                                                             └──Variable: check
                                                             └──Type expr: Variable: 9720
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 9720
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 9720
                                                    └──Desc: Variable
                                                       └──Variable: t
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: 9720
                                           └──Type expr: Constructor: option
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: 9720
                                        └──Desc: Function
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 9720
                                              └──Desc: Variable: t'
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: 9720
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Some
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: 9720
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 9720
                                                 └──Expression:
                                                    └──Type expr: Constructor: ex_alist
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: 9720
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 9720
                                                             └──Type expr: Constructor: ex_alist
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: 9720
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 9720
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: 9720
                                                                      └──Type expr: Constructor: ex_alist
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: 9720
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: alist
                                                                            └──Type expr: Variable: 9720
                                                                            └──Type expr: Variable: 9720
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 9720
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Constructor: succ
                                                                                     └──Type expr: Variable: 9720
                                                                               └──Type expr: Constructor: ex_alist
                                                                                  └──Type expr: Constructor: succ
                                                                                     └──Type expr: Variable: 9720
                                                                      └──Desc: Variable
                                                                         └──Variable: asnoc
                                                                         └──Type expr: Variable: 9720
                                                                         └──Type expr: Variable: 9720
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: alist
                                                                         └──Type expr: Variable: 9720
                                                                         └──Type expr: Variable: 9720
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Anil
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: alist
                                                                                  └──Type expr: Variable: 9720
                                                                                  └──Type expr: Variable: 9720
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 9720
                                                                └──Desc: Variable
                                                                   └──Variable: t'
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: 9720
                                                          └──Desc: Variable
                                                             └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: amgu
                └──Abstraction:
                   └──Variables: 9742
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 9773
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 9773
                            └──Type expr: Arrow
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Variable: 9773
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Variable: 9773
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 9773
                            └──Desc: Variable: s
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 9773
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Variable: 9773
                                  └──Type expr: Constructor: option
                                     └──Type expr: Constructor: ex_alist
                                        └──Type expr: Variable: 9773
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 9773
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: ex_alist
                                        └──Type expr: Variable: 9773
                                     └──Type expr: Constructor: option
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: 9773
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: 9773
                                        └──Desc: Variable: acc
                                     └──Expression:
                                        └──Type expr: Constructor: option
                                           └──Type expr: Constructor: ex_alist
                                              └──Type expr: Variable: 9773
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 9773
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 9773
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Variable: 9773
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 9773
                                                    └──Desc: Variable
                                                       └──Variable: s
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 9773
                                                    └──Desc: Variable
                                                       └──Variable: t
                                                 └──Expression:
                                                    └──Type expr: Constructor: ex_alist
                                                       └──Type expr: Variable: 9773
                                                    └──Desc: Variable
                                                       └──Variable: acc
                                           └──Type expr: Tuple
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 9773
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 9773
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Variable: 9773
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 9773
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 9773
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: 9773
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 9773
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Leaf
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 9773
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 9773
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Leaf
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 9773
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: 9773
                                                          └──Desc: Any
                                                 └──Expression:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: 9773
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Some
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: ex_alist
                                                                └──Type expr: Variable: 9773
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: 9773
                                                       └──Expression:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: 9773
                                                          └──Desc: Variable
                                                             └──Variable: acc
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 9773
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 9773
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: 9773
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 9773
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Leaf
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 9773
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 9773
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Fork
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 9773
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 9773
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 9773
                                                             └──Pattern:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 9773
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 9773
                                                                └──Desc: Any
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: 9773
                                                          └──Desc: Any
                                                 └──Expression:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: 9773
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: None
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: 9773
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 9773
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 9773
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: 9773
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 9773
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Fork
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 9773
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 9773
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 9773
                                                             └──Pattern:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 9773
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 9773
                                                                └──Desc: Any
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 9773
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Leaf
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 9773
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: 9773
                                                          └──Desc: Any
                                                 └──Expression:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: 9773
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: None
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: 9773
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 9773
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 9773
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: 9773
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 9773
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Fork
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 9773
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 9773
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 9773
                                                             └──Pattern:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 9773
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 9773
                                                                └──Desc: Tuple
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 9773
                                                                      └──Desc: Variable: s1
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 9773
                                                                      └──Desc: Variable: s2
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 9773
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Fork
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 9773
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 9773
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 9773
                                                             └──Pattern:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 9773
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 9773
                                                                └──Desc: Tuple
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 9773
                                                                      └──Desc: Variable: t1
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 9773
                                                                      └──Desc: Variable: t2
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: 9773
                                                          └──Desc: Any
                                                 └──Expression:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: 9773
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: 9773
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: ex_alist
                                                                      └──Type expr: Variable: 9773
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: 9773
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: ex_alist
                                                                         └──Type expr: Variable: 9773
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ex_alist
                                                                            └──Type expr: Variable: 9773
                                                                         └──Type expr: Constructor: option
                                                                            └──Type expr: Constructor: ex_alist
                                                                               └──Type expr: Variable: 9773
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: ex_alist
                                                                            └──Type expr: Variable: 9773
                                                                └──Desc: Variable
                                                                   └──Variable: bind
                                                                   └──Type expr: Constructor: ex_alist
                                                                      └──Type expr: Variable: 9773
                                                             └──Expression:
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: ex_alist
                                                                      └──Type expr: Variable: 9773
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ex_alist
                                                                            └──Type expr: Variable: 9773
                                                                         └──Type expr: Constructor: option
                                                                            └──Type expr: Constructor: ex_alist
                                                                               └──Type expr: Variable: 9773
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Variable: 9773
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: ex_alist
                                                                                     └──Type expr: Variable: 9773
                                                                                  └──Type expr: Constructor: option
                                                                                     └──Type expr: Constructor: ex_alist
                                                                                        └──Type expr: Variable: 9773
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: term
                                                                                        └──Type expr: Variable: 9773
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Variable: 9773
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Constructor: ex_alist
                                                                                              └──Type expr: Variable: 9773
                                                                                           └──Type expr: Constructor: option
                                                                                              └──Type expr: Constructor: ex_alist
                                                                                                 └──Type expr: Variable: 9773
                                                                                  └──Desc: Variable
                                                                                     └──Variable: amgu
                                                                                     └──Type expr: Variable: 9773
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: term
                                                                                     └──Type expr: Variable: 9773
                                                                                  └──Desc: Variable
                                                                                     └──Variable: s1
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 9773
                                                                            └──Desc: Variable
                                                                               └──Variable: t1
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ex_alist
                                                                         └──Type expr: Variable: 9773
                                                                      └──Desc: Variable
                                                                         └──Variable: acc
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: ex_alist
                                                                └──Type expr: Variable: 9773
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: 9773
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: 9773
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: ex_alist
                                                                         └──Type expr: Variable: 9773
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: ex_alist
                                                                            └──Type expr: Variable: 9773
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: 9773
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: 9773
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: ex_alist
                                                                                  └──Type expr: Variable: 9773
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: ex_alist
                                                                                     └──Type expr: Variable: 9773
                                                                      └──Desc: Variable
                                                                         └──Variable: amgu
                                                                         └──Type expr: Variable: 9773
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: 9773
                                                                      └──Desc: Variable
                                                                         └──Variable: s2
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: 9773
                                                                └──Desc: Variable
                                                                   └──Variable: t2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: term
                         └──Type expr: Variable: 10030
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 10030
                         └──Type expr: Constructor: option
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Variable: 10030
                   └──Desc: Variable: mgu
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: 10030
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 10030
                            └──Type expr: Constructor: option
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Variable: 10030
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: 10030
                            └──Desc: Variable: s
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: 10030
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Variable: 10030
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: 10030
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Constructor: ex_alist
                                        └──Type expr: Variable: 10030
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: ex_alist
                                              └──Type expr: Variable: 10030
                                           └──Type expr: Constructor: option
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Variable: 10030
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: 10030
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: ex_alist
                                                       └──Type expr: Variable: 10030
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: 10030
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: 10030
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: 10030
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: ex_alist
                                                                └──Type expr: Variable: 10030
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: 10030
                                                    └──Desc: Variable
                                                       └──Variable: amgu
                                                       └──Type expr: Variable: 10030
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: 10030
                                                    └──Desc: Variable
                                                       └──Variable: s
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: 10030
                                              └──Desc: Variable
                                                 └──Variable: t
                                     └──Expression:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: 10030
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Exists_alist
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: 10030
                                                    └──Type expr: Variable: 10030
                                              └──Constructor type:
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Variable: 10030
                                           └──Expression:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: 10030
                                                 └──Type expr: Variable: 10030
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Anil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: 10030
                                                          └──Type expr: Variable: 10030 |}]

