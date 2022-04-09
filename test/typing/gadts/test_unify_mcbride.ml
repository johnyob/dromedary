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
                         └──Type expr: Variable: a6274
                      └──Type expr: Constructor: is_succ
                         └──Type expr: Variable: a6274
                   └──Desc: Variable: fin_succ
                └──Abstraction:
                   └──Variables: a6274
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: a6274
                         └──Type expr: Constructor: is_succ
                            └──Type expr: Variable: a6274
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a6274
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Constructor: is_succ
                               └──Type expr: Variable: a6274
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: a6274
                                  └──Desc: Variable
                                     └──Variable: f
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a6274
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: a6274
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_zero
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a6274
                                           └──Pattern:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
                                     └──Expression:
                                        └──Type expr: Constructor: is_succ
                                           └──Type expr: Variable: a6274
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Is_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: is_succ
                                                    └──Type expr: Variable: a6274
                                           └──Expression:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: a6274
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a6315
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a6274
                                           └──Pattern:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: a6315
                                              └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Constructor: is_succ
                                           └──Type expr: Variable: a6274
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Is_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: is_succ
                                                    └──Type expr: Variable: a6274
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
                         └──Type expr: Variable: a6344
                      └──Type expr: Constructor: term
                         └──Type expr: Variable: a6344
                   └──Desc: Variable: var
                └──Abstraction:
                   └──Variables: a6344
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: a6344
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a6344
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a6344
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a6344
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Var
                                  └──Constructor argument type:
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Variable: a6344
                                  └──Constructor type:
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: a6344
                               └──Expression:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: a6344
                                  └──Desc: Variable
                                     └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: a6350
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: a6372
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: a6350
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a6372
                   └──Desc: Variable: lift
                └──Abstraction:
                   └──Variables: a6372,a6372,a6350
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a6350
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a6372
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a6350
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a6372
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a6350
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a6372
                            └──Desc: Variable: r
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a6350
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a6372
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: a6350
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a6372
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Var
                                        └──Constructor argument type:
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: a6372
                                        └──Constructor type:
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: a6372
                                     └──Expression:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: a6372
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a6350
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a6372
                                              └──Desc: Variable
                                                 └──Variable: r
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: a6350
                                              └──Desc: Variable
                                                 └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: pre_subst
                └──Abstraction:
                   └──Variables: a6418
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a6405
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a6418
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a6405
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a6418
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a6405
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a6418
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a6405
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a6418
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a6405
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a6418
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: a6405
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: a6405
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a6405
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a6405
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a6405
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a6405
                                                    └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a6418
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a6405
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a6418
                                                    └──Desc: Variable
                                                       └──Variable: f
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a6405
                                                    └──Desc: Variable
                                                       └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a6405
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Leaf
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a6405
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a6418
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Leaf
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a6418
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a6405
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fork
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a6405
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a6405
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a6405
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a6405
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a6405
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a6405
                                                          └──Desc: Variable: t1
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a6405
                                                          └──Desc: Variable: t2
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a6418
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fork
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a6418
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a6418
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a6418
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a6418
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a6418
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a6418
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a6405
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a6418
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: a6405
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a6418
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a6405
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a6418
                                                                      └──Desc: Variable
                                                                         └──Variable: pre_subst
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: a6405
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: a6418
                                                                      └──Desc: Variable
                                                                         └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a6405
                                                                └──Desc: Variable
                                                                   └──Variable: t1
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a6418
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a6405
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a6418
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: a6405
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a6418
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a6405
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a6418
                                                                      └──Desc: Variable
                                                                         └──Variable: pre_subst
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: a6405
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: a6418
                                                                      └──Desc: Variable
                                                                         └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a6405
                                                                └──Desc: Variable
                                                                   └──Variable: t2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: a6472
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a6474
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a6446
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a6472
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a6446
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a6474
                   └──Desc: Variable: comp_subst
                └──Abstraction:
                   └──Variables: a6446
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a6472
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a6474
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a6446
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a6472
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a6446
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a6474
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a6472
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a6474
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: a6446
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a6472
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: a6446
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a6474
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Variable: a6446
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: a6472
                                  └──Desc: Variable: g
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Variable: a6446
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: a6474
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: a6446
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: a6474
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a6472
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a6474
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a6472
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a6474
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a6472
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a6474
                                                    └──Desc: Variable
                                                       └──Variable: pre_subst
                                                       └──Type expr: Variable: a6474
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a6472
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a6474
                                                    └──Desc: Variable
                                                       └──Variable: f
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a6472
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a6446
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a6472
                                                    └──Desc: Variable
                                                       └──Variable: g
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a6446
                                                    └──Desc: Variable
                                                       └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: thin
                └──Abstraction:
                   └──Variables: a6496
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a6528
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a6528
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a6528
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a6528
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a6528
                               └──Type expr: Constructor: fin
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: a6528
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: a6528
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: a6528
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Variable: a6528
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: a6528
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a6528
                                              └──Desc: Variable
                                                 └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: a6528
                                              └──Desc: Variable
                                                 └──Variable: y
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a6528
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: a6528
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a6528
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a6528
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a6528
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a6528
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a6528
                                                    └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a6528
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fin_succ
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a6528
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a6528
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a6528
                                                    └──Desc: Variable
                                                       └──Variable: y
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a6528
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a6528
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a6528
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a6600
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a6528
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a6600
                                                          └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a6528
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a6528
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a6528
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fin_zero
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: unit
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a6528
                                                 └──Expression:
                                                    └──Type expr: Constructor: unit
                                                    └──Desc: Constant: ()
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a6528
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a6528
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a6528
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a6640
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a6528
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a6640
                                                          └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a6528
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a6637
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a6528
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a6637
                                                          └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a6528
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fin_succ
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a6528
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a6528
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a6528
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a6637
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a6528
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: a6640
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: a6637
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: a6528
                                                                └──Desc: Variable
                                                                   └──Variable: thin
                                                                   └──Type expr: Variable: a6637
                                                             └──Expression:
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: a6640
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a6637
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
                         └──Type expr: Variable: a6709
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a6709
                            └──Type expr: Constructor: option
                               └──Type expr: Variable: a6703
                         └──Type expr: Constructor: option
                            └──Type expr: Variable: a6703
                   └──Desc: Variable: bind
                └──Abstraction:
                   └──Variables: a6709,a6709,a6709
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: option
                            └──Type expr: Variable: a6709
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: a6709
                               └──Type expr: Constructor: option
                                  └──Type expr: Variable: a6703
                            └──Type expr: Constructor: option
                               └──Type expr: Variable: a6703
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: option
                               └──Type expr: Variable: a6709
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a6709
                                  └──Type expr: Constructor: option
                                     └──Type expr: Variable: a6703
                               └──Type expr: Constructor: option
                                  └──Type expr: Variable: a6703
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a6709
                                     └──Type expr: Constructor: option
                                        └──Type expr: Variable: a6703
                                  └──Desc: Variable: f
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Variable: a6703
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: option
                                           └──Type expr: Variable: a6709
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Constructor: option
                                        └──Type expr: Variable: a6709
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Variable: a6709
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: None
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Variable: a6709
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Variable: a6703
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: None
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Variable: a6703
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Variable: a6709
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Some
                                                    └──Constructor argument type:
                                                       └──Type expr: Variable: a6709
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Variable: a6709
                                                 └──Pattern:
                                                    └──Type expr: Variable: a6709
                                                    └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Variable: a6703
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: a6709
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Variable: a6703
                                                    └──Desc: Variable
                                                       └──Variable: f
                                                 └──Expression:
                                                    └──Type expr: Variable: a6709
                                                    └──Desc: Variable
                                                       └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: thick
                └──Abstraction:
                   └──Variables: a6729
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a6763
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a6763
                            └──Type expr: Constructor: option
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a6763
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a6763
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: a6763
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: a6763
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: a6763
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Variable: a6763
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Variable: a6763
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Variable: a6763
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a6763
                                              └──Desc: Variable
                                                 └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a6763
                                              └──Desc: Variable
                                                 └──Variable: y
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a6763
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a6763
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a6763
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a6763
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a6763
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a6763
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a6763
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a6763
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a6763
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: None
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a6763
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a6763
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a6763
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a6763
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a6763
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a6763
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a6841
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a6763
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a6841
                                                          └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a6763
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Some
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a6763
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a6763
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a6763
                                                    └──Desc: Variable
                                                       └──Variable: y
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a6763
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a6763
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a6763
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a6879
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a6763
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a6879
                                                          └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a6763
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a6763
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a6763
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Constructor: is_succ
                                                       └──Type expr: Variable: a6879
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a6879
                                                             └──Type expr: Constructor: is_succ
                                                                └──Type expr: Variable: a6879
                                                          └──Desc: Variable
                                                             └──Variable: fin_succ
                                                             └──Type expr: Variable: a6879
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a6879
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Type expr: Constructor: is_succ
                                                    └──Type expr: Variable: a6879
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Constructor: is_succ
                                                             └──Type expr: Variable: a6879
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Is_succ
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: unit
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: is_succ
                                                                      └──Type expr: Variable: a6879
                                                             └──Pattern:
                                                                └──Type expr: Constructor: unit
                                                                └──Desc: Constant: ()
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a6763
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Some
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: a6763
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: a6763
                                                             └──Expression:
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: a6763
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Fin_zero
                                                                      └──Constructor argument type:
                                                                         └──Type expr: Constructor: unit
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: a6763
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: unit
                                                                      └──Desc: Constant: ()
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a6763
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a6763
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a6763
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a6957
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a6763
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a6957
                                                          └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a6763
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Fin_succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a6954
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a6763
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a6954
                                                          └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a6763
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Constructor: is_succ
                                                       └──Type expr: Variable: a6957
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a6957
                                                             └──Type expr: Constructor: is_succ
                                                                └──Type expr: Variable: a6957
                                                          └──Desc: Variable
                                                             └──Variable: fin_succ
                                                             └──Type expr: Variable: a6957
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a6957
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Type expr: Constructor: is_succ
                                                    └──Type expr: Variable: a6957
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Constructor: is_succ
                                                             └──Type expr: Variable: a6957
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Is_succ
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: unit
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: is_succ
                                                                      └──Type expr: Variable: a6957
                                                             └──Pattern:
                                                                └──Type expr: Constructor: unit
                                                                └──Desc: Constant: ()
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a6763
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: a7058
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: a6763
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: a6763
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: option
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: a7058
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Variable: a7058
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Variable: a6763
                                                                            └──Type expr: Constructor: option
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Variable: a6763
                                                                      └──Desc: Variable
                                                                         └──Variable: bind
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: a7058
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: a7058
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Variable: a6954
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Variable: a7058
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: fin
                                                                                        └──Type expr: Variable: a6957
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: fin
                                                                                           └──Type expr: Variable: a6954
                                                                                        └──Type expr: Constructor: option
                                                                                           └──Type expr: Constructor: fin
                                                                                              └──Type expr: Variable: a7058
                                                                                  └──Desc: Variable
                                                                                     └──Variable: thick
                                                                                     └──Type expr: Variable: a7058
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Variable: a6957
                                                                                  └──Desc: Variable
                                                                                     └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: a6954
                                                                            └──Desc: Variable
                                                                               └──Variable: y
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: a7058
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: a6763
                                                                └──Desc: Function
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: a7058
                                                                      └──Desc: Variable: x
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: a6763
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Some
                                                                            └──Constructor argument type:
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Variable: a6763
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Variable: a6763
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: a6763
                                                                            └──Desc: Construct
                                                                               └──Constructor description:
                                                                                  └──Name: Fin_succ
                                                                                  └──Constructor argument type:
                                                                                     └──Type expr: Constructor: fin
                                                                                        └──Type expr: Variable: a7058
                                                                                  └──Constructor type:
                                                                                     └──Type expr: Constructor: fin
                                                                                        └──Type expr: Variable: a6763
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Variable: a7058
                                                                                  └──Desc: Variable
                                                                                     └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: check
                └──Abstraction:
                   └──Variables: a7082
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a7116
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a7116
                            └──Type expr: Constructor: option
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a7116
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a7116
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: a7116
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a7116
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: a7116
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: a7116
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: term
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a7116
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Constructor: term
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: a7116
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a7116
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a7116
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a7116
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a7116
                                                    └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a7116
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a7116
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a7116
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7116
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: a7116
                                                             └──Type expr: Arrow
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: a7116
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a7116
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a7116
                                                          └──Desc: Variable
                                                             └──Variable: bind
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a7116
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a7116
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Constructor: succ
                                                                         └──Type expr: Variable: a7116
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: a7116
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Constructor: succ
                                                                               └──Type expr: Variable: a7116
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Constructor: succ
                                                                                  └──Type expr: Variable: a7116
                                                                            └──Type expr: Constructor: option
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Variable: a7116
                                                                      └──Desc: Variable
                                                                         └──Variable: thick
                                                                         └──Type expr: Variable: a7116
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: a7116
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: a7116
                                                                └──Desc: Variable
                                                                   └──Variable: y
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a7116
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7116
                                                    └──Desc: Function
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a7116
                                                          └──Desc: Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a7116
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Some
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a7116
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a7116
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a7116
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Var
                                                                      └──Constructor argument type:
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Variable: a7116
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: a7116
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Variable: a7116
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a7116
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Leaf
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a7116
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a7116
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Some
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a7116
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7116
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a7116
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Leaf
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a7116
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a7116
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Fork
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a7116
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a7116
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a7116
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a7116
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a7116
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a7116
                                                          └──Desc: Variable: t1
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a7116
                                                          └──Desc: Variable: t2
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a7116
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7116
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a7116
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7116
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a7116
                                                             └──Type expr: Arrow
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a7116
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a7116
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a7116
                                                          └──Desc: Variable
                                                             └──Variable: bind
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a7116
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a7116
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Constructor: succ
                                                                         └──Type expr: Variable: a7116
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a7116
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Constructor: succ
                                                                               └──Type expr: Variable: a7116
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Constructor: succ
                                                                                  └──Type expr: Variable: a7116
                                                                            └──Type expr: Constructor: option
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Variable: a7116
                                                                      └──Desc: Variable
                                                                         └──Variable: check
                                                                         └──Type expr: Variable: a7116
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: a7116
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: a7116
                                                                └──Desc: Variable
                                                                   └──Variable: t1
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a7116
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7116
                                                    └──Desc: Function
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7116
                                                          └──Desc: Variable: t1
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a7116
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a7116
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: a7116
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a7116
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: option
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a7116
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Variable: a7116
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: term
                                                                                     └──Type expr: Variable: a7116
                                                                            └──Type expr: Constructor: option
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Variable: a7116
                                                                      └──Desc: Variable
                                                                         └──Variable: bind
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: a7116
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: a7116
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Constructor: succ
                                                                                     └──Type expr: Variable: a7116
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: term
                                                                                     └──Type expr: Variable: a7116
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: fin
                                                                                        └──Type expr: Constructor: succ
                                                                                           └──Type expr: Variable: a7116
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Constructor: succ
                                                                                              └──Type expr: Variable: a7116
                                                                                        └──Type expr: Constructor: option
                                                                                           └──Type expr: Constructor: term
                                                                                              └──Type expr: Variable: a7116
                                                                                  └──Desc: Variable
                                                                                     └──Variable: check
                                                                                     └──Type expr: Variable: a7116
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: fin
                                                                                     └──Type expr: Constructor: succ
                                                                                        └──Type expr: Variable: a7116
                                                                                  └──Desc: Variable
                                                                                     └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Constructor: succ
                                                                                  └──Type expr: Variable: a7116
                                                                            └──Desc: Variable
                                                                               └──Variable: t2
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a7116
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a7116
                                                                └──Desc: Function
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a7116
                                                                      └──Desc: Variable: t2
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: a7116
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Some
                                                                            └──Constructor argument type:
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Variable: a7116
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: term
                                                                                     └──Type expr: Variable: a7116
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a7116
                                                                            └──Desc: Construct
                                                                               └──Constructor description:
                                                                                  └──Name: Fork
                                                                                  └──Constructor argument type:
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Variable: a7116
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Variable: a7116
                                                                                  └──Constructor type:
                                                                                     └──Type expr: Constructor: term
                                                                                        └──Type expr: Variable: a7116
                                                                               └──Expression:
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Constructor: term
                                                                                        └──Type expr: Variable: a7116
                                                                                     └──Type expr: Constructor: term
                                                                                        └──Type expr: Variable: a7116
                                                                                  └──Desc: Tuple
                                                                                     └──Expression:
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Variable: a7116
                                                                                        └──Desc: Variable
                                                                                           └──Variable: t1
                                                                                     └──Expression:
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Variable: a7116
                                                                                        └──Desc: Variable
                                                                                           └──Variable: t2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: fin
                         └──Type expr: Constructor: succ
                            └──Type expr: Variable: a7371
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a7371
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a7371
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a7371
                   └──Desc: Variable: subst_var
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a7371
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a7371
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: a7371
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a7371
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a7371
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a7371
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: a7371
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a7371
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a7371
                                  └──Desc: Variable: t'
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: a7371
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: a7371
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a7371
                                        └──Desc: Variable: y
                                     └──Expression:
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: a7371
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a7371
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a7371
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a7371
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a7371
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: a7371
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: a7371
                                                          └──Desc: Variable
                                                             └──Variable: thick
                                                             └──Type expr: Variable: a7371
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a7371
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a7371
                                                    └──Desc: Variable
                                                       └──Variable: y
                                           └──Type expr: Constructor: option
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: a7371
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a7371
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: None
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: a7371
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a7371
                                                    └──Desc: Variable
                                                       └──Variable: t'
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a7371
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Some
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a7371
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: a7371
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a7371
                                                          └──Desc: Variable: y'
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a7371
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Var
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a7371
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a7371
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a7371
                                                          └──Desc: Variable
                                                             └──Variable: y'
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: fin
                         └──Type expr: Constructor: succ
                            └──Type expr: Variable: a7393
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a7393
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a7393
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a7393
                   └──Desc: Variable: subst
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a7393
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a7393
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: a7393
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a7393
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a7393
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a7393
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: term
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: a7393
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a7393
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a7393
                                  └──Desc: Variable: t'
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: term
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: a7393
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: a7393
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a7393
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a7393
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a7393
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a7393
                                        └──Desc: Variable
                                           └──Variable: pre_subst
                                           └──Type expr: Variable: a7393
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Variable: a7393
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: a7393
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a7393
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a7393
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a7393
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a7393
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7393
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a7393
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a7393
                                                    └──Desc: Variable
                                                       └──Variable: subst_var
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a7393
                                                    └──Desc: Variable
                                                       └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a7393
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
                   └──Variables: a7423,a7422
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: alist
                            └──Type expr: Variable: a7450
                            └──Type expr: Variable: a7451
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a7450
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a7451
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: a7450
                               └──Type expr: Variable: a7451
                            └──Desc: Variable: s
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a7450
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a7451
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: alist
                                     └──Type expr: Variable: a7450
                                     └──Type expr: Variable: a7451
                                  └──Desc: Variable
                                     └──Variable: s
                               └──Type expr: Constructor: alist
                                  └──Type expr: Variable: a7450
                                  └──Type expr: Variable: a7451
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Variable: a7450
                                           └──Type expr: Variable: a7451
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Anil
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: a7450
                                                    └──Type expr: Variable: a7451
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: a7450
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: a7451
                                        └──Desc: Variable
                                           └──Variable: var
                                           └──Type expr: Variable: a7450
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Variable: a7450
                                           └──Type expr: Variable: a7451
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Asnoc
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: a7516
                                                       └──Type expr: Variable: a7451
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a7516
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a7516
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: a7450
                                                    └──Type expr: Variable: a7451
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: a7516
                                                    └──Type expr: Variable: a7451
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a7516
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a7516
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: a7516
                                                       └──Type expr: Variable: a7451
                                                    └──Desc: Variable: s
                                                 └──Pattern:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a7516
                                                    └──Desc: Variable: t
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a7516
                                                    └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: a7450
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: a7451
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a7450
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a7516
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a7450
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a7451
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a7516
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7451
                                                       └──Type expr: Arrow
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a7450
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a7516
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a7450
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a7451
                                                    └──Desc: Variable
                                                       └──Variable: comp_subst
                                                       └──Type expr: Variable: a7450
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a7516
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a7451
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: alist
                                                                └──Type expr: Variable: a7516
                                                                └──Type expr: Variable: a7451
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: a7516
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a7451
                                                          └──Desc: Variable
                                                             └──Variable: sub
                                                             └──Type expr: Variable: a7451
                                                             └──Type expr: Variable: a7516
                                                       └──Expression:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: a7516
                                                             └──Type expr: Variable: a7451
                                                          └──Desc: Variable
                                                             └──Variable: s
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a7450
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a7516
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a7516
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a7450
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7516
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a7516
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a7516
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: a7450
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a7516
                                                          └──Desc: Variable
                                                             └──Variable: subst_var
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a7516
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a7516
                                                    └──Desc: Variable
                                                       └──Variable: t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: append
                └──Abstraction:
                   └──Variables: a7604,a7608,a7607
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: alist
                            └──Type expr: Variable: a7638
                            └──Type expr: Variable: a7639
                         └──Type expr: Arrow
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: a7650
                               └──Type expr: Variable: a7638
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: a7650
                               └──Type expr: Variable: a7639
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: a7638
                               └──Type expr: Variable: a7639
                            └──Desc: Variable: s1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: alist
                                  └──Type expr: Variable: a7650
                                  └──Type expr: Variable: a7638
                               └──Type expr: Constructor: alist
                                  └──Type expr: Variable: a7650
                                  └──Type expr: Variable: a7639
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: alist
                                     └──Type expr: Variable: a7650
                                     └──Type expr: Variable: a7638
                                  └──Desc: Variable: s2
                               └──Expression:
                                  └──Type expr: Constructor: alist
                                     └──Type expr: Variable: a7650
                                     └──Type expr: Variable: a7639
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Variable: a7650
                                           └──Type expr: Variable: a7638
                                        └──Desc: Variable
                                           └──Variable: s2
                                     └──Type expr: Constructor: alist
                                        └──Type expr: Variable: a7650
                                        └──Type expr: Variable: a7638
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: a7650
                                                 └──Type expr: Variable: a7638
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Anil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: a7650
                                                          └──Type expr: Variable: a7638
                                           └──Expression:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: a7650
                                                 └──Type expr: Variable: a7639
                                              └──Desc: Variable
                                                 └──Variable: s1
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: a7650
                                                 └──Type expr: Variable: a7638
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Asnoc
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: a7699
                                                             └──Type expr: Variable: a7638
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7699
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a7699
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: a7650
                                                          └──Type expr: Variable: a7638
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: a7699
                                                          └──Type expr: Variable: a7638
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a7699
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a7699
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: a7699
                                                             └──Type expr: Variable: a7638
                                                          └──Desc: Variable: s2
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7699
                                                          └──Desc: Variable: t
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a7699
                                                          └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: a7650
                                                 └──Type expr: Variable: a7639
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Asnoc
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: a7699
                                                             └──Type expr: Variable: a7639
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7699
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a7699
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: a7650
                                                          └──Type expr: Variable: a7639
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: a7699
                                                          └──Type expr: Variable: a7639
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a7699
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a7699
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: a7699
                                                             └──Type expr: Variable: a7639
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: alist
                                                                      └──Type expr: Variable: a7699
                                                                      └──Type expr: Variable: a7638
                                                                   └──Type expr: Constructor: alist
                                                                      └──Type expr: Variable: a7699
                                                                      └──Type expr: Variable: a7639
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: alist
                                                                            └──Type expr: Variable: a7638
                                                                            └──Type expr: Variable: a7639
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: alist
                                                                               └──Type expr: Variable: a7699
                                                                               └──Type expr: Variable: a7638
                                                                            └──Type expr: Constructor: alist
                                                                               └──Type expr: Variable: a7699
                                                                               └──Type expr: Variable: a7639
                                                                      └──Desc: Variable
                                                                         └──Variable: append
                                                                         └──Type expr: Variable: a7699
                                                                         └──Type expr: Variable: a7639
                                                                         └──Type expr: Variable: a7638
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: alist
                                                                         └──Type expr: Variable: a7638
                                                                         └──Type expr: Variable: a7639
                                                                      └──Desc: Variable
                                                                         └──Variable: s1
                                                             └──Expression:
                                                                └──Type expr: Constructor: alist
                                                                   └──Type expr: Variable: a7699
                                                                   └──Type expr: Variable: a7638
                                                                └──Desc: Variable
                                                                   └──Variable: s2
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7699
                                                          └──Desc: Variable
                                                             └──Variable: t
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a7699
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
                         └──Type expr: Variable: a7786
                         └──Type expr: Variable: a7785
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a7786
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a7786
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a7786
                   └──Desc: Variable: asnoc
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: alist
                            └──Type expr: Variable: a7786
                            └──Type expr: Variable: a7785
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a7786
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: a7786
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: a7786
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: a7786
                               └──Type expr: Variable: a7785
                            └──Desc: Variable: a
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a7786
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: a7786
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: a7786
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a7786
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: a7786
                                     └──Type expr: Constructor: ex_alist
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: a7786
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a7786
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a7786
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Exists_alist
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a7786
                                                    └──Type expr: Variable: a7785
                                              └──Constructor type:
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a7786
                                           └──Expression:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a7786
                                                 └──Type expr: Variable: a7785
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Asnoc
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: a7786
                                                             └──Type expr: Variable: a7785
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7786
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a7786
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a7786
                                                          └──Type expr: Variable: a7785
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: a7786
                                                          └──Type expr: Variable: a7785
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a7786
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a7786
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: a7786
                                                             └──Type expr: Variable: a7785
                                                          └──Desc: Variable
                                                             └──Variable: a
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a7786
                                                          └──Desc: Variable
                                                             └──Variable: t
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a7786
                                                          └──Desc: Variable
                                                             └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: weaken_fin
                └──Abstraction:
                   └──Variables: a7814
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Variable: a7835
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a7835
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a7835
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a7835
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Variable: a7835
                                  └──Desc: Variable
                                     └──Variable: f
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a7835
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: a7835
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_zero
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a7835
                                           └──Pattern:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
                                     └──Expression:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a7835
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_zero
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: unit
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a7835
                                           └──Expression:
                                              └──Type expr: Constructor: unit
                                              └──Desc: Constant: ()
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: a7835
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a7881
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a7835
                                           └──Pattern:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: a7881
                                              └──Desc: Variable: f
                                     └──Expression:
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a7835
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Fin_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a7835
                                              └──Constructor type:
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a7835
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: a7835
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a7881
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a7835
                                                    └──Desc: Variable
                                                       └──Variable: weaken_fin
                                                       └──Type expr: Variable: a7881
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a7881
                                                    └──Desc: Variable
                                                       └──Variable: f
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: term
                         └──Type expr: Variable: a7950
                      └──Type expr: Constructor: term
                         └──Type expr: Constructor: succ
                            └──Type expr: Variable: a7950
                   └──Desc: Variable: weaken_term
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a7950
                         └──Type expr: Constructor: term
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a7950
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a7950
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: term
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a7950
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: a7950
                                     └──Type expr: Constructor: term
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: a7950
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: a7950
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a7950
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a7950
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a7950
                                        └──Desc: Variable
                                           └──Variable: pre_subst
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a7950
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: a7950
                                           └──Type expr: Constructor: term
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Variable: a7950
                                        └──Desc: Function
                                           └──Pattern:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: a7950
                                              └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a7950
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Var
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a7950
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a7950
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a7950
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a7950
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a7950
                                                          └──Desc: Variable
                                                             └──Variable: weaken_fin
                                                             └──Type expr: Variable: a7950
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a7950
                                                          └──Desc: Variable
                                                             └──Variable: x
                               └──Expression:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a7950
                                  └──Desc: Variable
                                     └──Variable: t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: weaken_alist
                └──Abstraction:
                   └──Variables: a7965,a7964
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: alist
                            └──Type expr: Variable: a7992
                            └──Type expr: Variable: a7993
                         └──Type expr: Constructor: alist
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a7992
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a7993
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: alist
                               └──Type expr: Variable: a7992
                               └──Type expr: Variable: a7993
                            └──Desc: Variable: s
                         └──Expression:
                            └──Type expr: Constructor: alist
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a7992
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a7993
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: alist
                                     └──Type expr: Variable: a7992
                                     └──Type expr: Variable: a7993
                                  └──Desc: Variable
                                     └──Variable: s
                               └──Type expr: Constructor: alist
                                  └──Type expr: Variable: a7992
                                  └──Type expr: Variable: a7993
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Variable: a7992
                                           └──Type expr: Variable: a7993
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Anil
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: a7992
                                                    └──Type expr: Variable: a7993
                                     └──Expression:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a7992
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a7993
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Anil
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a7992
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a7992
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Variable: a7992
                                           └──Type expr: Variable: a7993
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Asnoc
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: a8058
                                                       └──Type expr: Variable: a7993
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a8058
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a8058
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: a7992
                                                    └──Type expr: Variable: a7993
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: a8058
                                                    └──Type expr: Variable: a7993
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a8058
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a8058
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: a8058
                                                       └──Type expr: Variable: a7993
                                                    └──Desc: Variable: s
                                                 └──Pattern:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a8058
                                                    └──Desc: Variable: t
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a8058
                                                    └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: alist
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a7992
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Variable: a7993
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Asnoc
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: a7992
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a7993
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a7992
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a7992
                                              └──Constructor type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a7992
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a7993
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: a7992
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a7993
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a7992
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a7992
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Variable: a7992
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a7993
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: alist
                                                                └──Type expr: Variable: a8058
                                                                └──Type expr: Variable: a7993
                                                             └──Type expr: Constructor: alist
                                                                └──Type expr: Variable: a7992
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a7993
                                                          └──Desc: Variable
                                                             └──Variable: weaken_alist
                                                             └──Type expr: Variable: a7993
                                                             └──Type expr: Variable: a8058
                                                       └──Expression:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: a8058
                                                             └──Type expr: Variable: a7993
                                                          └──Desc: Variable
                                                             └──Variable: s
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a7992
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a8058
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a7992
                                                          └──Desc: Variable
                                                             └──Variable: weaken_term
                                                             └──Type expr: Variable: a8058
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8058
                                                          └──Desc: Variable
                                                             └──Variable: t
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a7992
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a7992
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a7992
                                                          └──Desc: Variable
                                                             └──Variable: weaken_fin
                                                             └──Type expr: Variable: a7992
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a7992
                                                          └──Desc: Variable
                                                             └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: sub'
                └──Abstraction:
                   └──Variables: a8157
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ex_alist
                            └──Type expr: Variable: a8181
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Variable: a8181
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a8181
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Variable: a8181
                            └──Desc: Variable: e
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Variable: a8181
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a8181
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Variable: a8181
                                  └──Desc: Variable
                                     └──Variable: e
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Variable: a8181
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: a8181
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Exists_alist
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: a8181
                                                    └──Type expr: Variable: a8206
                                              └──Constructor type:
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Variable: a8181
                                           └──Pattern:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: a8181
                                                 └──Type expr: Variable: a8206
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Anil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: a8181
                                                          └──Type expr: Variable: a8206
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: a8181
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: a8181
                                        └──Desc: Variable
                                           └──Variable: var
                                           └──Type expr: Variable: a8181
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: a8181
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Exists_alist
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: a8181
                                                    └──Type expr: Variable: a8237
                                              └──Constructor type:
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Variable: a8181
                                           └──Pattern:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: a8181
                                                 └──Type expr: Variable: a8237
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Asnoc
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: a8256
                                                             └──Type expr: Variable: a8237
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8256
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a8256
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: a8181
                                                          └──Type expr: Variable: a8237
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: a8256
                                                          └──Type expr: Variable: a8237
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a8256
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8256
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: alist
                                                             └──Type expr: Variable: a8256
                                                             └──Type expr: Variable: a8237
                                                          └──Desc: Variable: s
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8256
                                                          └──Desc: Variable: t
                                                       └──Pattern:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a8256
                                                          └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: a8181
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: a8181
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a8181
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a8181
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a8181
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a8181
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a8181
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8181
                                                       └──Type expr: Arrow
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a8181
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a8181
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a8181
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a8181
                                                    └──Desc: Variable
                                                       └──Variable: comp_subst
                                                       └──Type expr: Variable: a8181
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a8181
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a8181
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: ex_alist
                                                                └──Type expr: Variable: a8181
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: a8181
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a8181
                                                          └──Desc: Variable
                                                             └──Variable: sub'
                                                             └──Type expr: Variable: a8181
                                                       └──Expression:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: a8181
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Exists_alist
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: alist
                                                                      └──Type expr: Variable: a8181
                                                                      └──Type expr: Constructor: succ
                                                                         └──Type expr: Variable: a8237
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: ex_alist
                                                                      └──Type expr: Variable: a8181
                                                             └──Expression:
                                                                └──Type expr: Constructor: alist
                                                                   └──Type expr: Variable: a8181
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: a8237
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: alist
                                                                            └──Type expr: Variable: a8256
                                                                            └──Type expr: Variable: a8237
                                                                         └──Type expr: Constructor: alist
                                                                            └──Type expr: Variable: a8181
                                                                            └──Type expr: Constructor: succ
                                                                               └──Type expr: Variable: a8237
                                                                      └──Desc: Variable
                                                                         └──Variable: weaken_alist
                                                                         └──Type expr: Variable: a8237
                                                                         └──Type expr: Variable: a8256
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: alist
                                                                         └──Type expr: Variable: a8256
                                                                         └──Type expr: Variable: a8237
                                                                      └──Desc: Variable
                                                                         └──Variable: s
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a8181
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a8181
                                              └──Desc: Function
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a8181
                                                    └──Desc: Variable: t'
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a8181
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a8256
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a8181
                                                          └──Desc: Variable
                                                             └──Variable: weaken_term
                                                             └──Type expr: Variable: a8256
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8256
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: a8181
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8256
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: a8256
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Variable: a8181
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a8256
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Constructor: succ
                                                                                     └──Type expr: Variable: a8256
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: term
                                                                                     └──Type expr: Variable: a8256
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: fin
                                                                                        └──Type expr: Variable: a8181
                                                                                     └──Type expr: Constructor: term
                                                                                        └──Type expr: Variable: a8256
                                                                            └──Desc: Variable
                                                                               └──Variable: subst_var
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: fin
                                                                               └──Type expr: Constructor: succ
                                                                                  └──Type expr: Variable: a8256
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a8256
                                                                      └──Desc: Variable
                                                                         └──Variable: t
                                                             └──Expression:
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: a8181
                                                                └──Desc: Variable
                                                                   └──Variable: t'
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: ex_alist
                         └──Type expr: Variable: a8384
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a8384
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a8384
                   └──Desc: Variable: subst'
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ex_alist
                            └──Type expr: Variable: a8384
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a8384
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a8384
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Variable: a8384
                            └──Desc: Variable: e
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a8384
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a8384
                            └──Desc: Application
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Arrow
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: a8384
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: a8384
                                     └──Type expr: Arrow
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: a8384
                                        └──Type expr: Constructor: term
                                           └──Type expr: Variable: a8384
                                  └──Desc: Variable
                                     └──Variable: pre_subst
                                     └──Type expr: Variable: a8384
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: fin
                                        └──Type expr: Variable: a8384
                                     └──Type expr: Constructor: term
                                        └──Type expr: Variable: a8384
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: ex_alist
                                              └──Type expr: Variable: a8384
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Variable: a8384
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a8384
                                        └──Desc: Variable
                                           └──Variable: sub'
                                           └──Type expr: Variable: a8384
                                     └──Expression:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: a8384
                                        └──Desc: Variable
                                           └──Variable: e
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: fin
                         └──Type expr: Constructor: succ
                            └──Type expr: Variable: a8448
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a8448
                         └──Type expr: Constructor: ex_alist
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a8448
                   └──Desc: Variable: flex_flex
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a8448
                         └──Type expr: Arrow
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a8448
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a8448
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a8448
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: fin
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: a8448
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: a8448
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: fin
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: a8448
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: a8448
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: option
                                           └──Type expr: Constructor: fin
                                              └──Type expr: Variable: a8448
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a8448
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a8448
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8448
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a8448
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Variable: a8448
                                                    └──Desc: Variable
                                                       └──Variable: thick
                                                       └──Type expr: Variable: a8448
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a8448
                                                    └──Desc: Variable
                                                       └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: fin
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a8448
                                              └──Desc: Variable
                                                 └──Variable: y
                                     └──Type expr: Constructor: option
                                        └──Type expr: Constructor: fin
                                           └──Type expr: Variable: a8448
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a8448
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Some
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Variable: a8448
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a8448
                                                 └──Pattern:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Variable: a8448
                                                    └──Desc: Variable: y'
                                           └──Expression:
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a8448
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: fin
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8448
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8448
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: term
                                                                └──Type expr: Variable: a8448
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: a8448
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: a8448
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: alist
                                                                      └──Type expr: Variable: a8448
                                                                      └──Type expr: Variable: a8448
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a8448
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: fin
                                                                            └──Type expr: Constructor: succ
                                                                               └──Type expr: Variable: a8448
                                                                         └──Type expr: Constructor: ex_alist
                                                                            └──Type expr: Constructor: succ
                                                                               └──Type expr: Variable: a8448
                                                                └──Desc: Variable
                                                                   └──Variable: asnoc
                                                                   └──Type expr: Variable: a8448
                                                                   └──Type expr: Variable: a8448
                                                             └──Expression:
                                                                └──Type expr: Constructor: alist
                                                                   └──Type expr: Variable: a8448
                                                                   └──Type expr: Variable: a8448
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Anil
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: alist
                                                                            └──Type expr: Variable: a8448
                                                                            └──Type expr: Variable: a8448
                                                       └──Expression:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8448
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Var
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: fin
                                                                      └──Type expr: Variable: a8448
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8448
                                                             └──Expression:
                                                                └──Type expr: Constructor: fin
                                                                   └──Type expr: Variable: a8448
                                                                └──Desc: Variable
                                                                   └──Variable: y'
                                                 └──Expression:
                                                    └──Type expr: Constructor: fin
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a8448
                                                    └──Desc: Variable
                                                       └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: fin
                                                    └──Type expr: Variable: a8448
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: None
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Variable: a8448
                                           └──Expression:
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a8448
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Exists_alist
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8448
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8448
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8448
                                                 └──Expression:
                                                    └──Type expr: Constructor: alist
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a8448
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a8448
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Anil
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: alist
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a8448
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a8448
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: fin
                         └──Type expr: Constructor: succ
                            └──Type expr: Variable: a8530
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a8530
                         └──Type expr: Constructor: option
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a8530
                   └──Desc: Variable: flex_rigid
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: fin
                            └──Type expr: Constructor: succ
                               └──Type expr: Variable: a8530
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a8530
                            └──Type expr: Constructor: option
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: a8530
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: fin
                               └──Type expr: Constructor: succ
                                  └──Type expr: Variable: a8530
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Variable: a8530
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: a8530
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Variable: a8530
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Constructor: ex_alist
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Variable: a8530
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a8530
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a8530
                                           └──Type expr: Constructor: option
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a8530
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a8530
                                                 └──Type expr: Arrow
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a8530
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a8530
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8530
                                              └──Desc: Variable
                                                 └──Variable: bind
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a8530
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a8530
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8530
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8530
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a8530
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Constructor: succ
                                                                      └──Type expr: Variable: a8530
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8530
                                                          └──Desc: Variable
                                                             └──Variable: check
                                                             └──Type expr: Variable: a8530
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a8530
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a8530
                                                    └──Desc: Variable
                                                       └──Variable: t
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: term
                                              └──Type expr: Variable: a8530
                                           └──Type expr: Constructor: option
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Constructor: succ
                                                    └──Type expr: Variable: a8530
                                        └──Desc: Function
                                           └──Pattern:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a8530
                                              └──Desc: Variable: t'
                                           └──Expression:
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Variable: a8530
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Some
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Constructor: succ
                                                             └──Type expr: Variable: a8530
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a8530
                                                 └──Expression:
                                                    └──Type expr: Constructor: ex_alist
                                                       └──Type expr: Constructor: succ
                                                          └──Type expr: Variable: a8530
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: fin
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a8530
                                                             └──Type expr: Constructor: ex_alist
                                                                └──Type expr: Constructor: succ
                                                                   └──Type expr: Variable: a8530
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8530
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: fin
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: a8530
                                                                      └──Type expr: Constructor: ex_alist
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: a8530
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: alist
                                                                            └──Type expr: Variable: a8530
                                                                            └──Type expr: Variable: a8530
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a8530
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: fin
                                                                                  └──Type expr: Constructor: succ
                                                                                     └──Type expr: Variable: a8530
                                                                               └──Type expr: Constructor: ex_alist
                                                                                  └──Type expr: Constructor: succ
                                                                                     └──Type expr: Variable: a8530
                                                                      └──Desc: Variable
                                                                         └──Variable: asnoc
                                                                         └──Type expr: Variable: a8530
                                                                         └──Type expr: Variable: a8530
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: alist
                                                                         └──Type expr: Variable: a8530
                                                                         └──Type expr: Variable: a8530
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Anil
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: alist
                                                                                  └──Type expr: Variable: a8530
                                                                                  └──Type expr: Variable: a8530
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a8530
                                                                └──Desc: Variable
                                                                   └──Variable: t'
                                                       └──Expression:
                                                          └──Type expr: Constructor: fin
                                                             └──Type expr: Constructor: succ
                                                                └──Type expr: Variable: a8530
                                                          └──Desc: Variable
                                                             └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: amgu
                └──Abstraction:
                   └──Variables: a8552
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a8583
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a8583
                            └──Type expr: Arrow
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Variable: a8583
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Variable: a8583
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a8583
                            └──Desc: Variable: s
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a8583
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Variable: a8583
                                  └──Type expr: Constructor: option
                                     └──Type expr: Constructor: ex_alist
                                        └──Type expr: Variable: a8583
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a8583
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: ex_alist
                                        └──Type expr: Variable: a8583
                                     └──Type expr: Constructor: option
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: a8583
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: a8583
                                        └──Desc: Variable: acc
                                     └──Expression:
                                        └──Type expr: Constructor: option
                                           └──Type expr: Constructor: ex_alist
                                              └──Type expr: Variable: a8583
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a8583
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a8583
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Variable: a8583
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a8583
                                                    └──Desc: Variable
                                                       └──Variable: s
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a8583
                                                    └──Desc: Variable
                                                       └──Variable: t
                                                 └──Expression:
                                                    └──Type expr: Constructor: ex_alist
                                                       └──Type expr: Variable: a8583
                                                    └──Desc: Variable
                                                       └──Variable: acc
                                           └──Type expr: Tuple
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a8583
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a8583
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Variable: a8583
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a8583
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a8583
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: a8583
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8583
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Leaf
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8583
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8583
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Leaf
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8583
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: a8583
                                                          └──Desc: Any
                                                 └──Expression:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: a8583
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Some
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: ex_alist
                                                                └──Type expr: Variable: a8583
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: a8583
                                                       └──Expression:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: a8583
                                                          └──Desc: Variable
                                                             └──Variable: acc
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a8583
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a8583
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: a8583
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8583
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Leaf
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8583
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8583
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Fork
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a8583
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a8583
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8583
                                                             └──Pattern:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8583
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8583
                                                                └──Desc: Any
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: a8583
                                                          └──Desc: Any
                                                 └──Expression:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: a8583
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: None
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: a8583
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a8583
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a8583
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: a8583
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8583
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Fork
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a8583
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a8583
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8583
                                                             └──Pattern:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8583
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8583
                                                                └──Desc: Any
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8583
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Leaf
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8583
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: a8583
                                                          └──Desc: Any
                                                 └──Expression:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: a8583
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: None
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: a8583
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a8583
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a8583
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: a8583
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8583
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Fork
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a8583
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a8583
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8583
                                                             └──Pattern:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8583
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8583
                                                                └──Desc: Tuple
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a8583
                                                                      └──Desc: Variable: s1
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a8583
                                                                      └──Desc: Variable: s2
                                                       └──Pattern:
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8583
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Fork
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a8583
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a8583
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8583
                                                             └──Pattern:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8583
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8583
                                                                └──Desc: Tuple
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a8583
                                                                      └──Desc: Variable: t1
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a8583
                                                                      └──Desc: Variable: t2
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ex_alist
                                                             └──Type expr: Variable: a8583
                                                          └──Desc: Any
                                                 └──Expression:
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: a8583
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: a8583
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: ex_alist
                                                                      └──Type expr: Variable: a8583
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: a8583
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Constructor: ex_alist
                                                                         └──Type expr: Variable: a8583
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ex_alist
                                                                            └──Type expr: Variable: a8583
                                                                         └──Type expr: Constructor: option
                                                                            └──Type expr: Constructor: ex_alist
                                                                               └──Type expr: Variable: a8583
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: ex_alist
                                                                            └──Type expr: Variable: a8583
                                                                └──Desc: Variable
                                                                   └──Variable: bind
                                                                   └──Type expr: Constructor: ex_alist
                                                                      └──Type expr: Variable: a8583
                                                             └──Expression:
                                                                └──Type expr: Constructor: option
                                                                   └──Type expr: Constructor: ex_alist
                                                                      └──Type expr: Variable: a8583
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: ex_alist
                                                                            └──Type expr: Variable: a8583
                                                                         └──Type expr: Constructor: option
                                                                            └──Type expr: Constructor: ex_alist
                                                                               └──Type expr: Variable: a8583
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: term
                                                                                  └──Type expr: Variable: a8583
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: ex_alist
                                                                                     └──Type expr: Variable: a8583
                                                                                  └──Type expr: Constructor: option
                                                                                     └──Type expr: Constructor: ex_alist
                                                                                        └──Type expr: Variable: a8583
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: term
                                                                                        └──Type expr: Variable: a8583
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: term
                                                                                           └──Type expr: Variable: a8583
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Constructor: ex_alist
                                                                                              └──Type expr: Variable: a8583
                                                                                           └──Type expr: Constructor: option
                                                                                              └──Type expr: Constructor: ex_alist
                                                                                                 └──Type expr: Variable: a8583
                                                                                  └──Desc: Variable
                                                                                     └──Variable: amgu
                                                                                     └──Type expr: Variable: a8583
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: term
                                                                                     └──Type expr: Variable: a8583
                                                                                  └──Desc: Variable
                                                                                     └──Variable: s1
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a8583
                                                                            └──Desc: Variable
                                                                               └──Variable: t1
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: ex_alist
                                                                         └──Type expr: Variable: a8583
                                                                      └──Desc: Variable
                                                                         └──Variable: acc
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: ex_alist
                                                                └──Type expr: Variable: a8583
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: a8583
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: term
                                                                      └──Type expr: Variable: a8583
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: ex_alist
                                                                         └──Type expr: Variable: a8583
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Constructor: ex_alist
                                                                            └──Type expr: Variable: a8583
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: term
                                                                            └──Type expr: Variable: a8583
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: term
                                                                               └──Type expr: Variable: a8583
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: ex_alist
                                                                                  └──Type expr: Variable: a8583
                                                                               └──Type expr: Constructor: option
                                                                                  └──Type expr: Constructor: ex_alist
                                                                                     └──Type expr: Variable: a8583
                                                                      └──Desc: Variable
                                                                         └──Variable: amgu
                                                                         └──Type expr: Variable: a8583
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: term
                                                                         └──Type expr: Variable: a8583
                                                                      └──Desc: Variable
                                                                         └──Variable: s2
                                                             └──Expression:
                                                                └──Type expr: Constructor: term
                                                                   └──Type expr: Variable: a8583
                                                                └──Desc: Variable
                                                                   └──Variable: t2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: term
                         └──Type expr: Variable: a8840
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a8840
                         └──Type expr: Constructor: option
                            └──Type expr: Constructor: ex_alist
                               └──Type expr: Variable: a8840
                   └──Desc: Variable: mgu
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: term
                            └──Type expr: Variable: a8840
                         └──Type expr: Arrow
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a8840
                            └──Type expr: Constructor: option
                               └──Type expr: Constructor: ex_alist
                                  └──Type expr: Variable: a8840
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: term
                               └──Type expr: Variable: a8840
                            └──Desc: Variable: s
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: term
                                  └──Type expr: Variable: a8840
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: ex_alist
                                     └──Type expr: Variable: a8840
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: term
                                     └──Type expr: Variable: a8840
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Constructor: ex_alist
                                        └──Type expr: Variable: a8840
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: ex_alist
                                              └──Type expr: Variable: a8840
                                           └──Type expr: Constructor: option
                                              └──Type expr: Constructor: ex_alist
                                                 └──Type expr: Variable: a8840
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: term
                                                    └──Type expr: Variable: a8840
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: ex_alist
                                                       └──Type expr: Variable: a8840
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Constructor: ex_alist
                                                          └──Type expr: Variable: a8840
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: term
                                                          └──Type expr: Variable: a8840
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: term
                                                             └──Type expr: Variable: a8840
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: ex_alist
                                                                └──Type expr: Variable: a8840
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Constructor: ex_alist
                                                                   └──Type expr: Variable: a8840
                                                    └──Desc: Variable
                                                       └──Variable: amgu
                                                       └──Type expr: Variable: a8840
                                                 └──Expression:
                                                    └──Type expr: Constructor: term
                                                       └──Type expr: Variable: a8840
                                                    └──Desc: Variable
                                                       └──Variable: s
                                           └──Expression:
                                              └──Type expr: Constructor: term
                                                 └──Type expr: Variable: a8840
                                              └──Desc: Variable
                                                 └──Variable: t
                                     └──Expression:
                                        └──Type expr: Constructor: ex_alist
                                           └──Type expr: Variable: a8840
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Exists_alist
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: alist
                                                    └──Type expr: Variable: a8840
                                                    └──Type expr: Variable: a8840
                                              └──Constructor type:
                                                 └──Type expr: Constructor: ex_alist
                                                    └──Type expr: Variable: a8840
                                           └──Expression:
                                              └──Type expr: Constructor: alist
                                                 └──Type expr: Variable: a8840
                                                 └──Type expr: Variable: a8840
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Anil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: alist
                                                          └──Type expr: Variable: a8840
                                                          └──Type expr: Variable: a8840 |}]

