open! Import
open Util

let%expect_test "omega-1" =
  let str =
    {|
      external hole : 'a. 'a = "%hole";;

      type zero = Zero;;
      type 'a succ = Succ of 'a;;

      type 'm nat = 
        | Zero constraint 'm = zero
        | Succ of 'n. 'n nat constraint 'm = 'n succ
      ;;

      type ('a, 'n) seq = 
        | Nil constraint 'n = zero
        | Cons of 'm. 'a * ('a, 'm) seq constraint 'n = 'm succ
      ;;

      let l1 = Cons (3, Cons (5, Nil));;

      type ('m, 'n, 'k) plus = 
        | Plus_zero of 'n nat constraint 'm = zero and 'n = 'k
        | Plus_succ of 'm1 'k1. ('m1, 'n, 'k1) plus constraint 'm = 'm1 succ and 'k = 'k1 succ
      ;;

      let rec (type 'a 'n) length = 
        fun (t : ('a, 'n) seq) ->
          (match t with
           ( Nil -> Zero
           | Cons (_, t) -> Succ (length t)
           ) 
          : 'n nat)
      ;;

      (* [('a, 'm, 'n) app] represents ['a seq] w/ length ['m + 'n], used for append *)
      type ('a, 'm, 'n) app = 
        | App of 'k. ('a, 'k) seq * ('m, 'n, 'k) plus
      ;;

      external hole : 'a. 'a = "%hole";;

      let rec (type 'a 'm 'n) append = 
        fun (t1 : ('a, 'm) seq) (t2 : ('a, 'n) seq) ->
          (match t1 with
           ( Nil -> App (t2, Plus_zero (length t2)) 
           | Cons (x, t1) ->
             match append t1 t2 with 
              (App (t1, plus) -> App (Cons (x, t1), Plus_succ plus)) 
           ) 
          : ('a, 'm, 'n) app) 
      ;;

      (* tip, node and fork kinds *)
      type tp;;
      type nd;;
      type ('a, 'b) fk;;

      type 'a shape = 
        | Tip constraint 'a = tp
        | Node constraint 'a = nd
        | Fork of 'b 'c. 'b shape * 'c shape constraint 'a = ('b, 'c) fk
      ;;

      (* true and false kinds *)
      type tt;;
      type ff;;
      type 'a boolean = 
        | Bool_true constraint 'a = tt
        | Bool_false constraint 'a = ff
      ;;

      type ('a, 'b) path = 
        | Path_none of 'b constraint 'a = tp
        | Path_here constraint 'a = nd
        | Path_left of 'x 'y. ('x, 'b) path constraint 'a = ('x, 'y) fk
        | Path_right of 'x 'y. ('y, 'b) path constraint 'a = ('x, 'y) fk
      ;; 

      type 'a list = 
        | Nil
        | Cons of 'a * 'a list
      ;;

      external map : 'a 'b. 'a list -> ('a -> 'b) -> 'b list = "%map";;

      type ('a, 'b) tree = 
        | Tree_tip constraint 'a = tp
        | Tree_node of 'b constraint 'a = nd
        | Tree_fork of 'x 'y. ('x, 'b) tree * ('y, 'b) tree constraint 'a = ('x, 'y) fk
      ;;

      let tree1 = Tree_fork (Tree_fork (Tree_tip, Tree_node 4), Tree_fork (Tree_node 4, Tree_node 3));;
      
      let rec app = fun t1 t2 -> 
        match t1 with
        ( Nil -> t2
        | Cons (x, t) -> Cons (x, app t1 t2)
        )
      ;;

      let rec (type 'a 'shape) find = 
        fun (eq : 'a -> 'a -> bool) (n : 'a) (t : ('shape, 'a) tree) -> 
          (match t with 
           ( Tree_tip -> Nil
           | Tree_node m ->
              if eq n m then Cons (Path_here, Nil) else Nil
           | Tree_fork (type 'x 'y) (l, r) ->
              (app (map (find eq n l) (fun x -> Path_left x)) 
                   (map (find eq n r) (fun x -> Path_right x))
              : (('x, 'y) fk, 'a) path list)
           )
          : ('shape, 'a) path list)   
      ;;

      let rec (type 'shape 'a) extract = 
        fun (p : ('shape, 'a) path) (t : ('shape, 'a) tree) ->
          (match (p, t) with
           ( (Path_none x, Tree_tip) -> x
           | (Path_here, Tree_node y) -> y
           | (Path_left p, Tree_fork (l, _)) -> extract p l
           | (Path_right p, Tree_fork (_, r)) -> extract p r
           )
          : 'a)
      ;;

      type ('m, 'n) le = 
        | Le_zero of 'n nat constraint 'm = zero
        | Le_succ of 'm1 'n1. ('m1, 'n1) le constraint 'm = 'm1 succ and 'n = 'n1 succ
      ;;

      type 'n even = 
        | Even_zero constraint 'n = zero
        | Even_ssucc of 'n1. 'n1 even constraint 'n = 'n1 succ succ
      ;;

      type one = zero succ;;
      type two = one succ;;
      type three = two succ;;
      type four = three succ;;

      let even0 = (Even_zero : zero even);;
      let even2 = (Even_ssucc even0 : two even);;
      let even4 = (Even_ssucc even2 : four even);;

      let p1 = (Plus_succ (Plus_succ (Plus_zero (Succ Zero))) : (two, one, three) plus);;

      let rec (type 'm 'n 'k) summand_less_than_sum = 
        fun (p : ('m, 'n, 'k) plus) ->
          (match p with
           ( Plus_succ p -> (Le_succ (summand_less_than_sum p))
           | Plus_zero n -> (Le_zero n : (zero, 'n) le)
           )
          : ('m, 'k) le)
      ;;
    |}
  in
  print_infer_result str;
  [%expect{|
    Structure:
    └──Structure:
       └──Structure item: Primitive
          └──Value description:
             └──Name: hole
             └──Scheme:
                └──Variables: a4669
                └──Type expr: Variable: a4669
             └──Primitive name: %hole
       └──Structure item: Type
          └──Type declaration:
             └──Type name: zero
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Zero
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: zero
       └──Structure item: Type
          └──Type declaration:
             └──Type name: succ
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Succ
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: a
       └──Structure item: Type
          └──Type declaration:
             └──Type name: nat
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Zero
                   └──Constructor alphas: m
                   └──Constructor type:
                      └──Type expr: Constructor: nat
                         └──Type expr: Variable: m
                   └──Constraint:
                      └──Type expr: Variable: m
                      └──Type expr: Constructor: zero
                └──Constructor declaration:
                   └──Constructor name: Succ
                   └──Constructor alphas: m
                   └──Constructor type:
                      └──Type expr: Constructor: nat
                         └──Type expr: Variable: m
                   └──Constructor argument:
                      └──Constructor betas: n
                      └──Type expr: Constructor: nat
                         └──Type expr: Variable: n
                   └──Constraint:
                      └──Type expr: Variable: m
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: n
       └──Structure item: Type
          └──Type declaration:
             └──Type name: seq
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: a n
                   └──Constructor type:
                      └──Type expr: Constructor: seq
                         └──Type expr: Variable: a
                         └──Type expr: Variable: n
                   └──Constraint:
                      └──Type expr: Variable: n
                      └──Type expr: Constructor: zero
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: a n
                   └──Constructor type:
                      └──Type expr: Constructor: seq
                         └──Type expr: Variable: a
                         └──Type expr: Variable: n
                   └──Constructor argument:
                      └──Constructor betas: m
                      └──Type expr: Tuple
                         └──Type expr: Variable: a
                         └──Type expr: Constructor: seq
                            └──Type expr: Variable: a
                            └──Type expr: Variable: m
                   └──Constraint:
                      └──Type expr: Variable: n
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: m
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: seq
                      └──Type expr: Constructor: int
                      └──Type expr: Constructor: succ
                         └──Type expr: Constructor: succ
                            └──Type expr: Constructor: zero
                   └──Desc: Variable: l1
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: seq
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: succ
                            └──Type expr: Constructor: succ
                               └──Type expr: Constructor: zero
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Cons
                            └──Constructor argument type:
                               └──Type expr: Tuple
                                  └──Type expr: Constructor: int
                                  └──Type expr: Constructor: seq
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Constructor: zero
                            └──Constructor type:
                               └──Type expr: Constructor: seq
                                  └──Type expr: Constructor: int
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Constructor: zero
                         └──Expression:
                            └──Type expr: Tuple
                               └──Type expr: Constructor: int
                               └──Type expr: Constructor: seq
                                  └──Type expr: Constructor: int
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Constructor: zero
                            └──Desc: Tuple
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Constant: 3
                               └──Expression:
                                  └──Type expr: Constructor: seq
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Constructor: zero
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Cons
                                        └──Constructor argument type:
                                           └──Type expr: Tuple
                                              └──Type expr: Constructor: int
                                              └──Type expr: Constructor: seq
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: zero
                                        └──Constructor type:
                                           └──Type expr: Constructor: seq
                                              └──Type expr: Constructor: int
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Constructor: zero
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: int
                                           └──Type expr: Constructor: seq
                                              └──Type expr: Constructor: int
                                              └──Type expr: Constructor: zero
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 5
                                           └──Expression:
                                              └──Type expr: Constructor: seq
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: zero
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: seq
                                                          └──Type expr: Constructor: int
                                                          └──Type expr: Constructor: zero
       └──Structure item: Type
          └──Type declaration:
             └──Type name: plus
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Plus_zero
                   └──Constructor alphas: m n k
                   └──Constructor type:
                      └──Type expr: Constructor: plus
                         └──Type expr: Variable: m
                         └──Type expr: Variable: n
                         └──Type expr: Variable: k
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: nat
                         └──Type expr: Variable: n
                   └──Constraint:
                      └──Type expr: Variable: m
                      └──Type expr: Constructor: zero
                   └──Constraint:
                      └──Type expr: Variable: n
                      └──Type expr: Variable: k
                └──Constructor declaration:
                   └──Constructor name: Plus_succ
                   └──Constructor alphas: m n k
                   └──Constructor type:
                      └──Type expr: Constructor: plus
                         └──Type expr: Variable: m
                         └──Type expr: Variable: n
                         └──Type expr: Variable: k
                   └──Constructor argument:
                      └──Constructor betas: m1 k1
                      └──Type expr: Constructor: plus
                         └──Type expr: Variable: m1
                         └──Type expr: Variable: n
                         └──Type expr: Variable: k1
                   └──Constraint:
                      └──Type expr: Variable: m
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: m1
                   └──Constraint:
                      └──Type expr: Variable: k
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: k1
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: length
                └──Abstraction:
                   └──Variables: a4718,a4717
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: seq
                            └──Type expr: Variable: a4740
                            └──Type expr: Variable: a4741
                         └──Type expr: Constructor: nat
                            └──Type expr: Variable: a4741
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: seq
                               └──Type expr: Variable: a4740
                               └──Type expr: Variable: a4741
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: nat
                               └──Type expr: Variable: a4741
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: seq
                                     └──Type expr: Variable: a4740
                                     └──Type expr: Variable: a4741
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: seq
                                  └──Type expr: Variable: a4740
                                  └──Type expr: Variable: a4741
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: seq
                                           └──Type expr: Variable: a4740
                                           └──Type expr: Variable: a4741
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Nil
                                              └──Constructor type:
                                                 └──Type expr: Constructor: seq
                                                    └──Type expr: Variable: a4740
                                                    └──Type expr: Variable: a4741
                                     └──Expression:
                                        └──Type expr: Constructor: nat
                                           └──Type expr: Variable: a4741
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Zero
                                              └──Constructor type:
                                                 └──Type expr: Constructor: nat
                                                    └──Type expr: Variable: a4741
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: seq
                                           └──Type expr: Variable: a4740
                                           └──Type expr: Variable: a4741
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Cons
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a4740
                                                    └──Type expr: Constructor: seq
                                                       └──Type expr: Variable: a4740
                                                       └──Type expr: Variable: a4778
                                              └──Constructor type:
                                                 └──Type expr: Constructor: seq
                                                    └──Type expr: Variable: a4740
                                                    └──Type expr: Variable: a4741
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a4740
                                                 └──Type expr: Constructor: seq
                                                    └──Type expr: Variable: a4740
                                                    └──Type expr: Variable: a4778
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Variable: a4740
                                                    └──Desc: Any
                                                 └──Pattern:
                                                    └──Type expr: Constructor: seq
                                                       └──Type expr: Variable: a4740
                                                       └──Type expr: Variable: a4778
                                                    └──Desc: Variable: t
                                     └──Expression:
                                        └──Type expr: Constructor: nat
                                           └──Type expr: Variable: a4741
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: nat
                                                    └──Type expr: Variable: a4778
                                              └──Constructor type:
                                                 └──Type expr: Constructor: nat
                                                    └──Type expr: Variable: a4741
                                           └──Expression:
                                              └──Type expr: Constructor: nat
                                                 └──Type expr: Variable: a4778
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: seq
                                                          └──Type expr: Variable: a4740
                                                          └──Type expr: Variable: a4778
                                                       └──Type expr: Constructor: nat
                                                          └──Type expr: Variable: a4778
                                                    └──Desc: Variable
                                                       └──Variable: length
                                                       └──Type expr: Variable: a4778
                                                       └──Type expr: Variable: a4740
                                                 └──Expression:
                                                    └──Type expr: Constructor: seq
                                                       └──Type expr: Variable: a4740
                                                       └──Type expr: Variable: a4778
                                                    └──Desc: Variable
                                                       └──Variable: t
       └──Structure item: Type
          └──Type declaration:
             └──Type name: app
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: App
                   └──Constructor alphas: a m n
                   └──Constructor type:
                      └──Type expr: Constructor: app
                         └──Type expr: Variable: a
                         └──Type expr: Variable: m
                         └──Type expr: Variable: n
                   └──Constructor argument:
                      └──Constructor betas: k
                      └──Type expr: Tuple
                         └──Type expr: Constructor: seq
                            └──Type expr: Variable: a
                            └──Type expr: Variable: k
                         └──Type expr: Constructor: plus
                            └──Type expr: Variable: m
                            └──Type expr: Variable: n
                            └──Type expr: Variable: k
       └──Structure item: Primitive
          └──Value description:
             └──Name: hole
             └──Scheme:
                └──Variables: a4813
                └──Type expr: Variable: a4813
             └──Primitive name: %hole
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: append
                └──Abstraction:
                   └──Variables: a4826,a4829,a4828
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: seq
                            └──Type expr: Variable: a4860
                            └──Type expr: Variable: a4861
                         └──Type expr: Arrow
                            └──Type expr: Constructor: seq
                               └──Type expr: Variable: a4860
                               └──Type expr: Variable: a4873
                            └──Type expr: Constructor: app
                               └──Type expr: Variable: a4860
                               └──Type expr: Variable: a4861
                               └──Type expr: Variable: a4873
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: seq
                               └──Type expr: Variable: a4860
                               └──Type expr: Variable: a4861
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: seq
                                  └──Type expr: Variable: a4860
                                  └──Type expr: Variable: a4873
                               └──Type expr: Constructor: app
                                  └──Type expr: Variable: a4860
                                  └──Type expr: Variable: a4861
                                  └──Type expr: Variable: a4873
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: seq
                                     └──Type expr: Variable: a4860
                                     └──Type expr: Variable: a4873
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Constructor: app
                                     └──Type expr: Variable: a4860
                                     └──Type expr: Variable: a4861
                                     └──Type expr: Variable: a4873
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: seq
                                           └──Type expr: Variable: a4860
                                           └──Type expr: Variable: a4861
                                        └──Desc: Variable
                                           └──Variable: t1
                                     └──Type expr: Constructor: seq
                                        └──Type expr: Variable: a4860
                                        └──Type expr: Variable: a4861
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: seq
                                                 └──Type expr: Variable: a4860
                                                 └──Type expr: Variable: a4861
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: seq
                                                          └──Type expr: Variable: a4860
                                                          └──Type expr: Variable: a4861
                                           └──Expression:
                                              └──Type expr: Constructor: app
                                                 └──Type expr: Variable: a4860
                                                 └──Type expr: Variable: a4861
                                                 └──Type expr: Variable: a4873
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: App
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: seq
                                                             └──Type expr: Variable: a4860
                                                             └──Type expr: Variable: a4873
                                                          └──Type expr: Constructor: plus
                                                             └──Type expr: Variable: a4861
                                                             └──Type expr: Variable: a4873
                                                             └──Type expr: Variable: a4873
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: app
                                                          └──Type expr: Variable: a4860
                                                          └──Type expr: Variable: a4861
                                                          └──Type expr: Variable: a4873
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: seq
                                                          └──Type expr: Variable: a4860
                                                          └──Type expr: Variable: a4873
                                                       └──Type expr: Constructor: plus
                                                          └──Type expr: Variable: a4861
                                                          └──Type expr: Variable: a4873
                                                          └──Type expr: Variable: a4873
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: seq
                                                             └──Type expr: Variable: a4860
                                                             └──Type expr: Variable: a4873
                                                          └──Desc: Variable
                                                             └──Variable: t2
                                                       └──Expression:
                                                          └──Type expr: Constructor: plus
                                                             └──Type expr: Variable: a4861
                                                             └──Type expr: Variable: a4873
                                                             └──Type expr: Variable: a4873
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Plus_zero
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: nat
                                                                      └──Type expr: Variable: a4873
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: plus
                                                                      └──Type expr: Variable: a4861
                                                                      └──Type expr: Variable: a4873
                                                                      └──Type expr: Variable: a4873
                                                             └──Expression:
                                                                └──Type expr: Constructor: nat
                                                                   └──Type expr: Variable: a4873
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: seq
                                                                            └──Type expr: Variable: a4860
                                                                            └──Type expr: Variable: a4873
                                                                         └──Type expr: Constructor: nat
                                                                            └──Type expr: Variable: a4873
                                                                      └──Desc: Variable
                                                                         └──Variable: length
                                                                         └──Type expr: Variable: a4873
                                                                         └──Type expr: Variable: a4860
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: seq
                                                                         └──Type expr: Variable: a4860
                                                                         └──Type expr: Variable: a4873
                                                                      └──Desc: Variable
                                                                         └──Variable: t2
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: seq
                                                 └──Type expr: Variable: a4860
                                                 └──Type expr: Variable: a4861
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a4860
                                                          └──Type expr: Constructor: seq
                                                             └──Type expr: Variable: a4860
                                                             └──Type expr: Variable: a4952
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: seq
                                                          └──Type expr: Variable: a4860
                                                          └──Type expr: Variable: a4861
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a4860
                                                       └──Type expr: Constructor: seq
                                                          └──Type expr: Variable: a4860
                                                          └──Type expr: Variable: a4952
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Variable: a4860
                                                          └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: seq
                                                             └──Type expr: Variable: a4860
                                                             └──Type expr: Variable: a4952
                                                          └──Desc: Variable: t1
                                           └──Expression:
                                              └──Type expr: Constructor: app
                                                 └──Type expr: Variable: a4860
                                                 └──Type expr: Variable: a4861
                                                 └──Type expr: Variable: a4873
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Constructor: app
                                                       └──Type expr: Variable: a4860
                                                       └──Type expr: Variable: a4952
                                                       └──Type expr: Variable: a4873
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: seq
                                                                └──Type expr: Variable: a4860
                                                                └──Type expr: Variable: a4873
                                                             └──Type expr: Constructor: app
                                                                └──Type expr: Variable: a4860
                                                                └──Type expr: Variable: a4952
                                                                └──Type expr: Variable: a4873
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: seq
                                                                      └──Type expr: Variable: a4860
                                                                      └──Type expr: Variable: a4952
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: seq
                                                                         └──Type expr: Variable: a4860
                                                                         └──Type expr: Variable: a4873
                                                                      └──Type expr: Constructor: app
                                                                         └──Type expr: Variable: a4860
                                                                         └──Type expr: Variable: a4952
                                                                         └──Type expr: Variable: a4873
                                                                └──Desc: Variable
                                                                   └──Variable: append
                                                                   └──Type expr: Variable: a4873
                                                                   └──Type expr: Variable: a4952
                                                                   └──Type expr: Variable: a4860
                                                             └──Expression:
                                                                └──Type expr: Constructor: seq
                                                                   └──Type expr: Variable: a4860
                                                                   └──Type expr: Variable: a4952
                                                                └──Desc: Variable
                                                                   └──Variable: t1
                                                       └──Expression:
                                                          └──Type expr: Constructor: seq
                                                             └──Type expr: Variable: a4860
                                                             └──Type expr: Variable: a4873
                                                          └──Desc: Variable
                                                             └──Variable: t2
                                                 └──Type expr: Constructor: app
                                                    └──Type expr: Variable: a4860
                                                    └──Type expr: Variable: a4952
                                                    └──Type expr: Variable: a4873
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Constructor: app
                                                             └──Type expr: Variable: a4860
                                                             └──Type expr: Variable: a4952
                                                             └──Type expr: Variable: a4873
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: App
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: seq
                                                                         └──Type expr: Variable: a4860
                                                                         └──Type expr: Variable: a4999
                                                                      └──Type expr: Constructor: plus
                                                                         └──Type expr: Variable: a4952
                                                                         └──Type expr: Variable: a4873
                                                                         └──Type expr: Variable: a4999
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: app
                                                                      └──Type expr: Variable: a4860
                                                                      └──Type expr: Variable: a4952
                                                                      └──Type expr: Variable: a4873
                                                             └──Pattern:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: seq
                                                                      └──Type expr: Variable: a4860
                                                                      └──Type expr: Variable: a4999
                                                                   └──Type expr: Constructor: plus
                                                                      └──Type expr: Variable: a4952
                                                                      └──Type expr: Variable: a4873
                                                                      └──Type expr: Variable: a4999
                                                                └──Desc: Tuple
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: seq
                                                                         └──Type expr: Variable: a4860
                                                                         └──Type expr: Variable: a4999
                                                                      └──Desc: Variable: t1
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: plus
                                                                         └──Type expr: Variable: a4952
                                                                         └──Type expr: Variable: a4873
                                                                         └──Type expr: Variable: a4999
                                                                      └──Desc: Variable: plus
                                                       └──Expression:
                                                          └──Type expr: Constructor: app
                                                             └──Type expr: Variable: a4860
                                                             └──Type expr: Variable: a4861
                                                             └──Type expr: Variable: a4873
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: App
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: seq
                                                                         └──Type expr: Variable: a4860
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: a4999
                                                                      └──Type expr: Constructor: plus
                                                                         └──Type expr: Variable: a4861
                                                                         └──Type expr: Variable: a4873
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: a4999
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: app
                                                                      └──Type expr: Variable: a4860
                                                                      └──Type expr: Variable: a4861
                                                                      └──Type expr: Variable: a4873
                                                             └──Expression:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: seq
                                                                      └──Type expr: Variable: a4860
                                                                      └──Type expr: Constructor: succ
                                                                         └──Type expr: Variable: a4999
                                                                   └──Type expr: Constructor: plus
                                                                      └──Type expr: Variable: a4861
                                                                      └──Type expr: Variable: a4873
                                                                      └──Type expr: Constructor: succ
                                                                         └──Type expr: Variable: a4999
                                                                └──Desc: Tuple
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: seq
                                                                         └──Type expr: Variable: a4860
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: a4999
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Cons
                                                                            └──Constructor argument type:
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: a4860
                                                                                  └──Type expr: Constructor: seq
                                                                                     └──Type expr: Variable: a4860
                                                                                     └──Type expr: Variable: a4999
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: seq
                                                                                  └──Type expr: Variable: a4860
                                                                                  └──Type expr: Constructor: succ
                                                                                     └──Type expr: Variable: a4999
                                                                         └──Expression:
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a4860
                                                                               └──Type expr: Constructor: seq
                                                                                  └──Type expr: Variable: a4860
                                                                                  └──Type expr: Variable: a4999
                                                                            └──Desc: Tuple
                                                                               └──Expression:
                                                                                  └──Type expr: Variable: a4860
                                                                                  └──Desc: Variable
                                                                                     └──Variable: x
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: seq
                                                                                     └──Type expr: Variable: a4860
                                                                                     └──Type expr: Variable: a4999
                                                                                  └──Desc: Variable
                                                                                     └──Variable: t1
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: plus
                                                                         └──Type expr: Variable: a4861
                                                                         └──Type expr: Variable: a4873
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: a4999
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Plus_succ
                                                                            └──Constructor argument type:
                                                                               └──Type expr: Constructor: plus
                                                                                  └──Type expr: Variable: a4952
                                                                                  └──Type expr: Variable: a4873
                                                                                  └──Type expr: Variable: a4999
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: plus
                                                                                  └──Type expr: Variable: a4861
                                                                                  └──Type expr: Variable: a4873
                                                                                  └──Type expr: Constructor: succ
                                                                                     └──Type expr: Variable: a4999
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: plus
                                                                               └──Type expr: Variable: a4952
                                                                               └──Type expr: Variable: a4873
                                                                               └──Type expr: Variable: a4999
                                                                            └──Desc: Variable
                                                                               └──Variable: plus
       └──Structure item: Type
          └──Type declaration:
             └──Type name: tp
             └──Type declaration kind: Abstract
       └──Structure item: Type
          └──Type declaration:
             └──Type name: nd
             └──Type declaration kind: Abstract
       └──Structure item: Type
          └──Type declaration:
             └──Type name: fk
             └──Type declaration kind: Abstract
       └──Structure item: Type
          └──Type declaration:
             └──Type name: shape
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Tip
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: shape
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: tp
                └──Constructor declaration:
                   └──Constructor name: Node
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: shape
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: nd
                └──Constructor declaration:
                   └──Constructor name: Fork
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: shape
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas: b c
                      └──Type expr: Tuple
                         └──Type expr: Constructor: shape
                            └──Type expr: Variable: b
                         └──Type expr: Constructor: shape
                            └──Type expr: Variable: c
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: fk
                         └──Type expr: Variable: b
                         └──Type expr: Variable: c
       └──Structure item: Type
          └──Type declaration:
             └──Type name: tt
             └──Type declaration kind: Abstract
       └──Structure item: Type
          └──Type declaration:
             └──Type name: ff
             └──Type declaration kind: Abstract
       └──Structure item: Type
          └──Type declaration:
             └──Type name: boolean
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Bool_true
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: boolean
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: tt
                └──Constructor declaration:
                   └──Constructor name: Bool_false
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: boolean
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: ff
       └──Structure item: Type
          └──Type declaration:
             └──Type name: path
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Path_none
                   └──Constructor alphas: a b
                   └──Constructor type:
                      └──Type expr: Constructor: path
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: b
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: tp
                └──Constructor declaration:
                   └──Constructor name: Path_here
                   └──Constructor alphas: a b
                   └──Constructor type:
                      └──Type expr: Constructor: path
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: nd
                └──Constructor declaration:
                   └──Constructor name: Path_left
                   └──Constructor alphas: a b
                   └──Constructor type:
                      └──Type expr: Constructor: path
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                   └──Constructor argument:
                      └──Constructor betas: x y
                      └──Type expr: Constructor: path
                         └──Type expr: Variable: x
                         └──Type expr: Variable: b
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: fk
                         └──Type expr: Variable: x
                         └──Type expr: Variable: y
                └──Constructor declaration:
                   └──Constructor name: Path_right
                   └──Constructor alphas: a b
                   └──Constructor type:
                      └──Type expr: Constructor: path
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                   └──Constructor argument:
                      └──Constructor betas: x y
                      └──Type expr: Constructor: path
                         └──Type expr: Variable: y
                         └──Type expr: Variable: b
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: fk
                         └──Type expr: Variable: x
                         └──Type expr: Variable: y
       └──Structure item: Type
          └──Type declaration:
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: a
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a
       └──Structure item: Primitive
          └──Value description:
             └──Name: map
             └──Scheme:
                └──Variables: a5071,a5070
                └──Type expr: Arrow
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: a5070
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: a5070
                         └──Type expr: Variable: a5071
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a5071
             └──Primitive name: %map
       └──Structure item: Type
          └──Type declaration:
             └──Type name: tree
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Tree_tip
                   └──Constructor alphas: a b
                   └──Constructor type:
                      └──Type expr: Constructor: tree
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: tp
                └──Constructor declaration:
                   └──Constructor name: Tree_node
                   └──Constructor alphas: a b
                   └──Constructor type:
                      └──Type expr: Constructor: tree
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: b
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: nd
                └──Constructor declaration:
                   └──Constructor name: Tree_fork
                   └──Constructor alphas: a b
                   └──Constructor type:
                      └──Type expr: Constructor: tree
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                   └──Constructor argument:
                      └──Constructor betas: x y
                      └──Type expr: Tuple
                         └──Type expr: Constructor: tree
                            └──Type expr: Variable: x
                            └──Type expr: Variable: b
                         └──Type expr: Constructor: tree
                            └──Type expr: Variable: y
                            └──Type expr: Variable: b
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: fk
                         └──Type expr: Variable: x
                         └──Type expr: Variable: y
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: tree
                      └──Type expr: Constructor: fk
                         └──Type expr: Constructor: fk
                            └──Type expr: Constructor: tp
                            └──Type expr: Constructor: nd
                         └──Type expr: Constructor: fk
                            └──Type expr: Constructor: nd
                            └──Type expr: Constructor: nd
                      └──Type expr: Constructor: int
                   └──Desc: Variable: tree1
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: tree
                         └──Type expr: Constructor: fk
                            └──Type expr: Constructor: fk
                               └──Type expr: Constructor: tp
                               └──Type expr: Constructor: nd
                            └──Type expr: Constructor: fk
                               └──Type expr: Constructor: nd
                               └──Type expr: Constructor: nd
                         └──Type expr: Constructor: int
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Tree_fork
                            └──Constructor argument type:
                               └──Type expr: Tuple
                                  └──Type expr: Constructor: tree
                                     └──Type expr: Constructor: fk
                                        └──Type expr: Constructor: tp
                                        └──Type expr: Constructor: nd
                                     └──Type expr: Constructor: int
                                  └──Type expr: Constructor: tree
                                     └──Type expr: Constructor: fk
                                        └──Type expr: Constructor: nd
                                        └──Type expr: Constructor: nd
                                     └──Type expr: Constructor: int
                            └──Constructor type:
                               └──Type expr: Constructor: tree
                                  └──Type expr: Constructor: fk
                                     └──Type expr: Constructor: fk
                                        └──Type expr: Constructor: tp
                                        └──Type expr: Constructor: nd
                                     └──Type expr: Constructor: fk
                                        └──Type expr: Constructor: nd
                                        └──Type expr: Constructor: nd
                                  └──Type expr: Constructor: int
                         └──Expression:
                            └──Type expr: Tuple
                               └──Type expr: Constructor: tree
                                  └──Type expr: Constructor: fk
                                     └──Type expr: Constructor: tp
                                     └──Type expr: Constructor: nd
                                  └──Type expr: Constructor: int
                               └──Type expr: Constructor: tree
                                  └──Type expr: Constructor: fk
                                     └──Type expr: Constructor: nd
                                     └──Type expr: Constructor: nd
                                  └──Type expr: Constructor: int
                            └──Desc: Tuple
                               └──Expression:
                                  └──Type expr: Constructor: tree
                                     └──Type expr: Constructor: fk
                                        └──Type expr: Constructor: tp
                                        └──Type expr: Constructor: nd
                                     └──Type expr: Constructor: int
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Tree_fork
                                        └──Constructor argument type:
                                           └──Type expr: Tuple
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Constructor: tp
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Constructor: nd
                                                 └──Type expr: Constructor: int
                                        └──Constructor type:
                                           └──Type expr: Constructor: tree
                                              └──Type expr: Constructor: fk
                                                 └──Type expr: Constructor: tp
                                                 └──Type expr: Constructor: nd
                                              └──Type expr: Constructor: int
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: tree
                                              └──Type expr: Constructor: tp
                                              └──Type expr: Constructor: int
                                           └──Type expr: Constructor: tree
                                              └──Type expr: Constructor: nd
                                              └──Type expr: Constructor: int
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Constructor: tp
                                                 └──Type expr: Constructor: int
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Tree_tip
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Constructor: tp
                                                          └──Type expr: Constructor: int
                                           └──Expression:
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Constructor: nd
                                                 └──Type expr: Constructor: int
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Tree_node
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: int
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Constructor: nd
                                                          └──Type expr: Constructor: int
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 4
                               └──Expression:
                                  └──Type expr: Constructor: tree
                                     └──Type expr: Constructor: fk
                                        └──Type expr: Constructor: nd
                                        └──Type expr: Constructor: nd
                                     └──Type expr: Constructor: int
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Tree_fork
                                        └──Constructor argument type:
                                           └──Type expr: Tuple
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Constructor: nd
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Constructor: nd
                                                 └──Type expr: Constructor: int
                                        └──Constructor type:
                                           └──Type expr: Constructor: tree
                                              └──Type expr: Constructor: fk
                                                 └──Type expr: Constructor: nd
                                                 └──Type expr: Constructor: nd
                                              └──Type expr: Constructor: int
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: tree
                                              └──Type expr: Constructor: nd
                                              └──Type expr: Constructor: int
                                           └──Type expr: Constructor: tree
                                              └──Type expr: Constructor: nd
                                              └──Type expr: Constructor: int
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Constructor: nd
                                                 └──Type expr: Constructor: int
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Tree_node
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: int
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Constructor: nd
                                                          └──Type expr: Constructor: int
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 4
                                           └──Expression:
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Constructor: nd
                                                 └──Type expr: Constructor: int
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Tree_node
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: int
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Constructor: nd
                                                          └──Type expr: Constructor: int
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 3
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: app
                └──Abstraction:
                   └──Variables: a5191
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a5191
                         └──Type expr: Arrow
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a5191
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a5191
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a5191
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a5191
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a5191
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: a5191
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: a5191
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Variable: a5191
                                        └──Desc: Variable
                                           └──Variable: t1
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: a5191
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a5191
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a5191
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a5191
                                              └──Desc: Variable
                                                 └──Variable: t2
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a5191
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a5191
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a5191
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a5191
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a5191
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a5191
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Variable: a5191
                                                          └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a5191
                                                          └──Desc: Variable: t
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a5191
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a5191
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a5191
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a5191
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a5191
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a5191
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Variable: a5191
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a5191
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: a5191
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: a5191
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Variable: a5191
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: a5191
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: a5191
                                                                      └──Desc: Variable
                                                                         └──Variable: app
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Variable: a5191
                                                                      └──Desc: Variable
                                                                         └──Variable: t1
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a5191
                                                                └──Desc: Variable
                                                                   └──Variable: t2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: find
                └──Abstraction:
                   └──Variables: a5225,a5230
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a5277
                            └──Type expr: Arrow
                               └──Type expr: Variable: a5277
                               └──Type expr: Constructor: bool
                         └──Type expr: Arrow
                            └──Type expr: Variable: a5277
                            └──Type expr: Arrow
                               └──Type expr: Constructor: tree
                                  └──Type expr: Variable: a5295
                                  └──Type expr: Variable: a5277
                               └──Type expr: Constructor: list
                                  └──Type expr: Constructor: path
                                     └──Type expr: Variable: a5295
                                     └──Type expr: Variable: a5277
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a5277
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a5277
                                  └──Type expr: Constructor: bool
                            └──Desc: Variable: eq
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a5277
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: tree
                                     └──Type expr: Variable: a5295
                                     └──Type expr: Variable: a5277
                                  └──Type expr: Constructor: list
                                     └──Type expr: Constructor: path
                                        └──Type expr: Variable: a5295
                                        └──Type expr: Variable: a5277
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: a5277
                                  └──Desc: Variable: n
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: tree
                                        └──Type expr: Variable: a5295
                                        └──Type expr: Variable: a5277
                                     └──Type expr: Constructor: list
                                        └──Type expr: Constructor: path
                                           └──Type expr: Variable: a5295
                                           └──Type expr: Variable: a5277
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: tree
                                           └──Type expr: Variable: a5295
                                           └──Type expr: Variable: a5277
                                        └──Desc: Variable: t
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Constructor: path
                                              └──Type expr: Variable: a5295
                                              └──Type expr: Variable: a5277
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Variable: a5295
                                                 └──Type expr: Variable: a5277
                                              └──Desc: Variable
                                                 └──Variable: t
                                           └──Type expr: Constructor: tree
                                              └──Type expr: Variable: a5295
                                              └──Type expr: Variable: a5277
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a5295
                                                       └──Type expr: Variable: a5277
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Tree_tip
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a5295
                                                                └──Type expr: Variable: a5277
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: path
                                                          └──Type expr: Variable: a5295
                                                          └──Type expr: Variable: a5277
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Nil
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: path
                                                                   └──Type expr: Variable: a5295
                                                                   └──Type expr: Variable: a5277
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a5295
                                                       └──Type expr: Variable: a5277
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Tree_node
                                                          └──Constructor argument type:
                                                             └──Type expr: Variable: a5277
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a5295
                                                                └──Type expr: Variable: a5277
                                                       └──Pattern:
                                                          └──Type expr: Variable: a5277
                                                          └──Desc: Variable: m
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: path
                                                          └──Type expr: Variable: a5295
                                                          └──Type expr: Variable: a5277
                                                    └──Desc: If
                                                       └──Expression:
                                                          └──Type expr: Constructor: bool
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: a5277
                                                                   └──Type expr: Constructor: bool
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: a5277
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Variable: a5277
                                                                            └──Type expr: Constructor: bool
                                                                      └──Desc: Variable
                                                                         └──Variable: eq
                                                                   └──Expression:
                                                                      └──Type expr: Variable: a5277
                                                                      └──Desc: Variable
                                                                         └──Variable: n
                                                             └──Expression:
                                                                └──Type expr: Variable: a5277
                                                                └──Desc: Variable
                                                                   └──Variable: m
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: path
                                                                └──Type expr: Variable: a5295
                                                                └──Type expr: Variable: a5277
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Cons
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: path
                                                                         └──Type expr: Variable: a5295
                                                                         └──Type expr: Variable: a5277
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: path
                                                                            └──Type expr: Variable: a5295
                                                                            └──Type expr: Variable: a5277
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: path
                                                                         └──Type expr: Variable: a5295
                                                                         └──Type expr: Variable: a5277
                                                             └──Expression:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: path
                                                                      └──Type expr: Variable: a5295
                                                                      └──Type expr: Variable: a5277
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: path
                                                                         └──Type expr: Variable: a5295
                                                                         └──Type expr: Variable: a5277
                                                                └──Desc: Tuple
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: path
                                                                         └──Type expr: Variable: a5295
                                                                         └──Type expr: Variable: a5277
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Path_here
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: path
                                                                                  └──Type expr: Variable: a5295
                                                                                  └──Type expr: Variable: a5277
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: path
                                                                            └──Type expr: Variable: a5295
                                                                            └──Type expr: Variable: a5277
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Nil
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: path
                                                                                     └──Type expr: Variable: a5295
                                                                                     └──Type expr: Variable: a5277
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: path
                                                                └──Type expr: Variable: a5295
                                                                └──Type expr: Variable: a5277
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Nil
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: path
                                                                         └──Type expr: Variable: a5295
                                                                         └──Type expr: Variable: a5277
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a5295
                                                       └──Type expr: Variable: a5277
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Tree_fork
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a5399
                                                                   └──Type expr: Variable: a5277
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a5397
                                                                   └──Type expr: Variable: a5277
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a5295
                                                                └──Type expr: Variable: a5277
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a5399
                                                                └──Type expr: Variable: a5277
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a5397
                                                                └──Type expr: Variable: a5277
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a5399
                                                                   └──Type expr: Variable: a5277
                                                                └──Desc: Variable: l
                                                             └──Pattern:
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a5397
                                                                   └──Type expr: Variable: a5277
                                                                └──Desc: Variable: r
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: path
                                                          └──Type expr: Variable: a5295
                                                          └──Type expr: Variable: a5277
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: path
                                                                   └──Type expr: Constructor: fk
                                                                      └──Type expr: Variable: a5399
                                                                      └──Type expr: Variable: a5397
                                                                   └──Type expr: Variable: a5277
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: path
                                                                   └──Type expr: Constructor: fk
                                                                      └──Type expr: Variable: a5399
                                                                      └──Type expr: Variable: a5397
                                                                   └──Type expr: Variable: a5277
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: path
                                                                         └──Type expr: Constructor: fk
                                                                            └──Type expr: Variable: a5399
                                                                            └──Type expr: Variable: a5397
                                                                         └──Type expr: Variable: a5277
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: path
                                                                            └──Type expr: Constructor: fk
                                                                               └──Type expr: Variable: a5399
                                                                               └──Type expr: Variable: a5397
                                                                            └──Type expr: Variable: a5277
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: path
                                                                            └──Type expr: Constructor: fk
                                                                               └──Type expr: Variable: a5399
                                                                               └──Type expr: Variable: a5397
                                                                            └──Type expr: Variable: a5277
                                                                └──Desc: Variable
                                                                   └──Variable: app
                                                                   └──Type expr: Constructor: path
                                                                      └──Type expr: Constructor: fk
                                                                         └──Type expr: Variable: a5399
                                                                         └──Type expr: Variable: a5397
                                                                      └──Type expr: Variable: a5277
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: path
                                                                      └──Type expr: Constructor: fk
                                                                         └──Type expr: Variable: a5399
                                                                         └──Type expr: Variable: a5397
                                                                      └──Type expr: Variable: a5277
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: path
                                                                               └──Type expr: Variable: a5399
                                                                               └──Type expr: Variable: a5277
                                                                            └──Type expr: Constructor: path
                                                                               └──Type expr: Constructor: fk
                                                                                  └──Type expr: Variable: a5399
                                                                                  └──Type expr: Variable: a5397
                                                                               └──Type expr: Variable: a5277
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: path
                                                                               └──Type expr: Constructor: fk
                                                                                  └──Type expr: Variable: a5399
                                                                                  └──Type expr: Variable: a5397
                                                                               └──Type expr: Variable: a5277
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: path
                                                                                     └──Type expr: Variable: a5399
                                                                                     └──Type expr: Variable: a5277
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: path
                                                                                        └──Type expr: Variable: a5399
                                                                                        └──Type expr: Variable: a5277
                                                                                     └──Type expr: Constructor: path
                                                                                        └──Type expr: Constructor: fk
                                                                                           └──Type expr: Variable: a5399
                                                                                           └──Type expr: Variable: a5397
                                                                                        └──Type expr: Variable: a5277
                                                                                  └──Type expr: Constructor: list
                                                                                     └──Type expr: Constructor: path
                                                                                        └──Type expr: Constructor: fk
                                                                                           └──Type expr: Variable: a5399
                                                                                           └──Type expr: Variable: a5397
                                                                                        └──Type expr: Variable: a5277
                                                                            └──Desc: Variable
                                                                               └──Variable: map
                                                                               └──Type expr: Constructor: path
                                                                                  └──Type expr: Constructor: fk
                                                                                     └──Type expr: Variable: a5399
                                                                                     └──Type expr: Variable: a5397
                                                                                  └──Type expr: Variable: a5277
                                                                               └──Type expr: Constructor: path
                                                                                  └──Type expr: Variable: a5399
                                                                                  └──Type expr: Variable: a5277
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: path
                                                                                  └──Type expr: Variable: a5399
                                                                                  └──Type expr: Variable: a5277
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: tree
                                                                                        └──Type expr: Variable: a5399
                                                                                        └──Type expr: Variable: a5277
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Constructor: path
                                                                                           └──Type expr: Variable: a5399
                                                                                           └──Type expr: Variable: a5277
                                                                                  └──Desc: Application
                                                                                     └──Expression:
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Variable: a5277
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Constructor: tree
                                                                                                 └──Type expr: Variable: a5399
                                                                                                 └──Type expr: Variable: a5277
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Constructor: path
                                                                                                    └──Type expr: Variable: a5399
                                                                                                    └──Type expr: Variable: a5277
                                                                                        └──Desc: Application
                                                                                           └──Expression:
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Variable: a5277
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Variable: a5277
                                                                                                       └──Type expr: Constructor: bool
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Variable: a5277
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Constructor: tree
                                                                                                          └──Type expr: Variable: a5399
                                                                                                          └──Type expr: Variable: a5277
                                                                                                       └──Type expr: Constructor: list
                                                                                                          └──Type expr: Constructor: path
                                                                                                             └──Type expr: Variable: a5399
                                                                                                             └──Type expr: Variable: a5277
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: find
                                                                                                 └──Type expr: Variable: a5399
                                                                                                 └──Type expr: Variable: a5277
                                                                                           └──Expression:
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Variable: a5277
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Variable: a5277
                                                                                                    └──Type expr: Constructor: bool
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: eq
                                                                                     └──Expression:
                                                                                        └──Type expr: Variable: a5277
                                                                                        └──Desc: Variable
                                                                                           └──Variable: n
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: tree
                                                                                     └──Type expr: Variable: a5399
                                                                                     └──Type expr: Variable: a5277
                                                                                  └──Desc: Variable
                                                                                     └──Variable: l
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: path
                                                                            └──Type expr: Variable: a5399
                                                                            └──Type expr: Variable: a5277
                                                                         └──Type expr: Constructor: path
                                                                            └──Type expr: Constructor: fk
                                                                               └──Type expr: Variable: a5399
                                                                               └──Type expr: Variable: a5397
                                                                            └──Type expr: Variable: a5277
                                                                      └──Desc: Function
                                                                         └──Pattern:
                                                                            └──Type expr: Constructor: path
                                                                               └──Type expr: Variable: a5399
                                                                               └──Type expr: Variable: a5277
                                                                            └──Desc: Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: path
                                                                               └──Type expr: Constructor: fk
                                                                                  └──Type expr: Variable: a5399
                                                                                  └──Type expr: Variable: a5397
                                                                               └──Type expr: Variable: a5277
                                                                            └──Desc: Construct
                                                                               └──Constructor description:
                                                                                  └──Name: Path_left
                                                                                  └──Constructor argument type:
                                                                                     └──Type expr: Constructor: path
                                                                                        └──Type expr: Variable: a5399
                                                                                        └──Type expr: Variable: a5277
                                                                                  └──Constructor type:
                                                                                     └──Type expr: Constructor: path
                                                                                        └──Type expr: Constructor: fk
                                                                                           └──Type expr: Variable: a5399
                                                                                           └──Type expr: Variable: a5397
                                                                                        └──Type expr: Variable: a5277
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: path
                                                                                     └──Type expr: Variable: a5399
                                                                                     └──Type expr: Variable: a5277
                                                                                  └──Desc: Variable
                                                                                     └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: path
                                                                └──Type expr: Constructor: fk
                                                                   └──Type expr: Variable: a5399
                                                                   └──Type expr: Variable: a5397
                                                                └──Type expr: Variable: a5277
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: path
                                                                         └──Type expr: Variable: a5397
                                                                         └──Type expr: Variable: a5277
                                                                      └──Type expr: Constructor: path
                                                                         └──Type expr: Constructor: fk
                                                                            └──Type expr: Variable: a5399
                                                                            └──Type expr: Variable: a5397
                                                                         └──Type expr: Variable: a5277
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: path
                                                                         └──Type expr: Constructor: fk
                                                                            └──Type expr: Variable: a5399
                                                                            └──Type expr: Variable: a5397
                                                                         └──Type expr: Variable: a5277
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: path
                                                                               └──Type expr: Variable: a5397
                                                                               └──Type expr: Variable: a5277
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: path
                                                                                  └──Type expr: Variable: a5397
                                                                                  └──Type expr: Variable: a5277
                                                                               └──Type expr: Constructor: path
                                                                                  └──Type expr: Constructor: fk
                                                                                     └──Type expr: Variable: a5399
                                                                                     └──Type expr: Variable: a5397
                                                                                  └──Type expr: Variable: a5277
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: path
                                                                                  └──Type expr: Constructor: fk
                                                                                     └──Type expr: Variable: a5399
                                                                                     └──Type expr: Variable: a5397
                                                                                  └──Type expr: Variable: a5277
                                                                      └──Desc: Variable
                                                                         └──Variable: map
                                                                         └──Type expr: Constructor: path
                                                                            └──Type expr: Constructor: fk
                                                                               └──Type expr: Variable: a5399
                                                                               └──Type expr: Variable: a5397
                                                                            └──Type expr: Variable: a5277
                                                                         └──Type expr: Constructor: path
                                                                            └──Type expr: Variable: a5397
                                                                            └──Type expr: Variable: a5277
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: path
                                                                            └──Type expr: Variable: a5397
                                                                            └──Type expr: Variable: a5277
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: tree
                                                                                  └──Type expr: Variable: a5397
                                                                                  └──Type expr: Variable: a5277
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: path
                                                                                     └──Type expr: Variable: a5397
                                                                                     └──Type expr: Variable: a5277
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Variable: a5277
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: tree
                                                                                           └──Type expr: Variable: a5397
                                                                                           └──Type expr: Variable: a5277
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Constructor: path
                                                                                              └──Type expr: Variable: a5397
                                                                                              └──Type expr: Variable: a5277
                                                                                  └──Desc: Application
                                                                                     └──Expression:
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Variable: a5277
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Variable: a5277
                                                                                                 └──Type expr: Constructor: bool
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Variable: a5277
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Constructor: tree
                                                                                                    └──Type expr: Variable: a5397
                                                                                                    └──Type expr: Variable: a5277
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: path
                                                                                                       └──Type expr: Variable: a5397
                                                                                                       └──Type expr: Variable: a5277
                                                                                        └──Desc: Variable
                                                                                           └──Variable: find
                                                                                           └──Type expr: Variable: a5397
                                                                                           └──Type expr: Variable: a5277
                                                                                     └──Expression:
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Variable: a5277
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Variable: a5277
                                                                                              └──Type expr: Constructor: bool
                                                                                        └──Desc: Variable
                                                                                           └──Variable: eq
                                                                               └──Expression:
                                                                                  └──Type expr: Variable: a5277
                                                                                  └──Desc: Variable
                                                                                     └──Variable: n
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: tree
                                                                               └──Type expr: Variable: a5397
                                                                               └──Type expr: Variable: a5277
                                                                            └──Desc: Variable
                                                                               └──Variable: r
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: path
                                                                      └──Type expr: Variable: a5397
                                                                      └──Type expr: Variable: a5277
                                                                   └──Type expr: Constructor: path
                                                                      └──Type expr: Constructor: fk
                                                                         └──Type expr: Variable: a5399
                                                                         └──Type expr: Variable: a5397
                                                                      └──Type expr: Variable: a5277
                                                                └──Desc: Function
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: path
                                                                         └──Type expr: Variable: a5397
                                                                         └──Type expr: Variable: a5277
                                                                      └──Desc: Variable: x
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: path
                                                                         └──Type expr: Constructor: fk
                                                                            └──Type expr: Variable: a5399
                                                                            └──Type expr: Variable: a5397
                                                                         └──Type expr: Variable: a5277
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Path_right
                                                                            └──Constructor argument type:
                                                                               └──Type expr: Constructor: path
                                                                                  └──Type expr: Variable: a5397
                                                                                  └──Type expr: Variable: a5277
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: path
                                                                                  └──Type expr: Constructor: fk
                                                                                     └──Type expr: Variable: a5399
                                                                                     └──Type expr: Variable: a5397
                                                                                  └──Type expr: Variable: a5277
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: path
                                                                               └──Type expr: Variable: a5397
                                                                               └──Type expr: Variable: a5277
                                                                            └──Desc: Variable
                                                                               └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: extract
                └──Abstraction:
                   └──Variables: a5574,a5573
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: path
                            └──Type expr: Variable: a5600
                            └──Type expr: Variable: a5601
                         └──Type expr: Arrow
                            └──Type expr: Constructor: tree
                               └──Type expr: Variable: a5600
                               └──Type expr: Variable: a5601
                            └──Type expr: Variable: a5601
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: path
                               └──Type expr: Variable: a5600
                               └──Type expr: Variable: a5601
                            └──Desc: Variable: p
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: tree
                                  └──Type expr: Variable: a5600
                                  └──Type expr: Variable: a5601
                               └──Type expr: Variable: a5601
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: tree
                                     └──Type expr: Variable: a5600
                                     └──Type expr: Variable: a5601
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Variable: a5601
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: path
                                              └──Type expr: Variable: a5600
                                              └──Type expr: Variable: a5601
                                           └──Type expr: Constructor: tree
                                              └──Type expr: Variable: a5600
                                              └──Type expr: Variable: a5601
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: path
                                                 └──Type expr: Variable: a5600
                                                 └──Type expr: Variable: a5601
                                              └──Desc: Variable
                                                 └──Variable: p
                                           └──Expression:
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Variable: a5600
                                                 └──Type expr: Variable: a5601
                                              └──Desc: Variable
                                                 └──Variable: t
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: path
                                           └──Type expr: Variable: a5600
                                           └──Type expr: Variable: a5601
                                        └──Type expr: Constructor: tree
                                           └──Type expr: Variable: a5600
                                           └──Type expr: Variable: a5601
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: path
                                                    └──Type expr: Variable: a5600
                                                    └──Type expr: Variable: a5601
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a5600
                                                    └──Type expr: Variable: a5601
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: path
                                                       └──Type expr: Variable: a5600
                                                       └──Type expr: Variable: a5601
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Path_none
                                                          └──Constructor argument type:
                                                             └──Type expr: Variable: a5601
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: path
                                                                └──Type expr: Variable: a5600
                                                                └──Type expr: Variable: a5601
                                                       └──Pattern:
                                                          └──Type expr: Variable: a5601
                                                          └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a5600
                                                       └──Type expr: Variable: a5601
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Tree_tip
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a5600
                                                                └──Type expr: Variable: a5601
                                           └──Expression:
                                              └──Type expr: Variable: a5601
                                              └──Desc: Variable
                                                 └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: path
                                                    └──Type expr: Variable: a5600
                                                    └──Type expr: Variable: a5601
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a5600
                                                    └──Type expr: Variable: a5601
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: path
                                                       └──Type expr: Variable: a5600
                                                       └──Type expr: Variable: a5601
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Path_here
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: path
                                                                └──Type expr: Variable: a5600
                                                                └──Type expr: Variable: a5601
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a5600
                                                       └──Type expr: Variable: a5601
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Tree_node
                                                          └──Constructor argument type:
                                                             └──Type expr: Variable: a5601
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a5600
                                                                └──Type expr: Variable: a5601
                                                       └──Pattern:
                                                          └──Type expr: Variable: a5601
                                                          └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Variable: a5601
                                              └──Desc: Variable
                                                 └──Variable: y
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: path
                                                    └──Type expr: Variable: a5600
                                                    └──Type expr: Variable: a5601
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a5600
                                                    └──Type expr: Variable: a5601
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: path
                                                       └──Type expr: Variable: a5600
                                                       └──Type expr: Variable: a5601
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Path_left
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: path
                                                                └──Type expr: Variable: a5679
                                                                └──Type expr: Variable: a5601
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: path
                                                                └──Type expr: Variable: a5600
                                                                └──Type expr: Variable: a5601
                                                       └──Pattern:
                                                          └──Type expr: Constructor: path
                                                             └──Type expr: Variable: a5679
                                                             └──Type expr: Variable: a5601
                                                          └──Desc: Variable: p
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a5600
                                                       └──Type expr: Variable: a5601
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Tree_fork
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a5676
                                                                   └──Type expr: Variable: a5601
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a5674
                                                                   └──Type expr: Variable: a5601
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a5600
                                                                └──Type expr: Variable: a5601
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a5676
                                                                └──Type expr: Variable: a5601
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a5674
                                                                └──Type expr: Variable: a5601
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a5676
                                                                   └──Type expr: Variable: a5601
                                                                └──Desc: Variable: l
                                                             └──Pattern:
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a5674
                                                                   └──Type expr: Variable: a5601
                                                                └──Desc: Any
                                           └──Expression:
                                              └──Type expr: Variable: a5601
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: a5676
                                                          └──Type expr: Variable: a5601
                                                       └──Type expr: Variable: a5601
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: path
                                                                └──Type expr: Variable: a5676
                                                                └──Type expr: Variable: a5601
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a5676
                                                                   └──Type expr: Variable: a5601
                                                                └──Type expr: Variable: a5601
                                                          └──Desc: Variable
                                                             └──Variable: extract
                                                             └──Type expr: Variable: a5601
                                                             └──Type expr: Variable: a5676
                                                       └──Expression:
                                                          └──Type expr: Constructor: path
                                                             └──Type expr: Variable: a5676
                                                             └──Type expr: Variable: a5601
                                                          └──Desc: Variable
                                                             └──Variable: p
                                                 └──Expression:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a5676
                                                       └──Type expr: Variable: a5601
                                                    └──Desc: Variable
                                                       └──Variable: l
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: path
                                                    └──Type expr: Variable: a5600
                                                    └──Type expr: Variable: a5601
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a5600
                                                    └──Type expr: Variable: a5601
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: path
                                                       └──Type expr: Variable: a5600
                                                       └──Type expr: Variable: a5601
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Path_right
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: path
                                                                └──Type expr: Variable: a5732
                                                                └──Type expr: Variable: a5601
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: path
                                                                └──Type expr: Variable: a5600
                                                                └──Type expr: Variable: a5601
                                                       └──Pattern:
                                                          └──Type expr: Constructor: path
                                                             └──Type expr: Variable: a5732
                                                             └──Type expr: Variable: a5601
                                                          └──Desc: Variable: p
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a5600
                                                       └──Type expr: Variable: a5601
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Tree_fork
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a5729
                                                                   └──Type expr: Variable: a5601
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a5727
                                                                   └──Type expr: Variable: a5601
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a5600
                                                                └──Type expr: Variable: a5601
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a5729
                                                                └──Type expr: Variable: a5601
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a5727
                                                                └──Type expr: Variable: a5601
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a5729
                                                                   └──Type expr: Variable: a5601
                                                                └──Desc: Any
                                                             └──Pattern:
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a5727
                                                                   └──Type expr: Variable: a5601
                                                                └──Desc: Variable: r
                                           └──Expression:
                                              └──Type expr: Variable: a5601
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: a5727
                                                          └──Type expr: Variable: a5601
                                                       └──Type expr: Variable: a5601
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: path
                                                                └──Type expr: Variable: a5727
                                                                └──Type expr: Variable: a5601
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a5727
                                                                   └──Type expr: Variable: a5601
                                                                └──Type expr: Variable: a5601
                                                          └──Desc: Variable
                                                             └──Variable: extract
                                                             └──Type expr: Variable: a5601
                                                             └──Type expr: Variable: a5727
                                                       └──Expression:
                                                          └──Type expr: Constructor: path
                                                             └──Type expr: Variable: a5727
                                                             └──Type expr: Variable: a5601
                                                          └──Desc: Variable
                                                             └──Variable: p
                                                 └──Expression:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a5727
                                                       └──Type expr: Variable: a5601
                                                    └──Desc: Variable
                                                       └──Variable: r
       └──Structure item: Type
          └──Type declaration:
             └──Type name: le
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Le_zero
                   └──Constructor alphas: m n
                   └──Constructor type:
                      └──Type expr: Constructor: le
                         └──Type expr: Variable: m
                         └──Type expr: Variable: n
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: nat
                         └──Type expr: Variable: n
                   └──Constraint:
                      └──Type expr: Variable: m
                      └──Type expr: Constructor: zero
                └──Constructor declaration:
                   └──Constructor name: Le_succ
                   └──Constructor alphas: m n
                   └──Constructor type:
                      └──Type expr: Constructor: le
                         └──Type expr: Variable: m
                         └──Type expr: Variable: n
                   └──Constructor argument:
                      └──Constructor betas: m1 n1
                      └──Type expr: Constructor: le
                         └──Type expr: Variable: m1
                         └──Type expr: Variable: n1
                   └──Constraint:
                      └──Type expr: Variable: m
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: m1
                   └──Constraint:
                      └──Type expr: Variable: n
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: n1
       └──Structure item: Type
          └──Type declaration:
             └──Type name: even
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Even_zero
                   └──Constructor alphas: n
                   └──Constructor type:
                      └──Type expr: Constructor: even
                         └──Type expr: Variable: n
                   └──Constraint:
                      └──Type expr: Variable: n
                      └──Type expr: Constructor: zero
                └──Constructor declaration:
                   └──Constructor name: Even_ssucc
                   └──Constructor alphas: n
                   └──Constructor type:
                      └──Type expr: Constructor: even
                         └──Type expr: Variable: n
                   └──Constructor argument:
                      └──Constructor betas: n1
                      └──Type expr: Constructor: even
                         └──Type expr: Variable: n1
                   └──Constraint:
                      └──Type expr: Variable: n
                      └──Type expr: Constructor: succ
                         └──Type expr: Constructor: succ
                            └──Type expr: Variable: n1
       └──Structure item: Type
          └──Type declaration:
             └──Type name: one
             └──Type declaration kind: Alias
                └──Alias
                   └──Alias name: one
                   └──Alias alphas:
                   └──Type expr: Constructor: succ
                      └──Type expr: Constructor: zero
       └──Structure item: Type
          └──Type declaration:
             └──Type name: two
             └──Type declaration kind: Alias
                └──Alias
                   └──Alias name: two
                   └──Alias alphas:
                   └──Type expr: Constructor: succ
                      └──Type expr: Constructor: one
       └──Structure item: Type
          └──Type declaration:
             └──Type name: three
             └──Type declaration kind: Alias
                └──Alias
                   └──Alias name: three
                   └──Alias alphas:
                   └──Type expr: Constructor: succ
                      └──Type expr: Constructor: two
       └──Structure item: Type
          └──Type declaration:
             └──Type name: four
             └──Type declaration kind: Alias
                └──Alias
                   └──Alias name: four
                   └──Alias alphas:
                   └──Type expr: Constructor: succ
                      └──Type expr: Constructor: three
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: even
                      └──Type expr: Constructor: zero
                   └──Desc: Variable: even0
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: even
                         └──Type expr: Constructor: zero
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Even_zero
                            └──Constructor type:
                               └──Type expr: Constructor: even
                                  └──Type expr: Constructor: zero
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: even
                      └──Type expr: Constructor: two
                   └──Desc: Variable: even2
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: even
                         └──Type expr: Constructor: two
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Even_ssucc
                            └──Constructor argument type:
                               └──Type expr: Constructor: even
                                  └──Type expr: Constructor: zero
                            └──Constructor type:
                               └──Type expr: Constructor: even
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Constructor: zero
                         └──Expression:
                            └──Type expr: Constructor: even
                               └──Type expr: Constructor: zero
                            └──Desc: Variable
                               └──Variable: even0
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: even
                      └──Type expr: Constructor: four
                   └──Desc: Variable: even4
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: even
                         └──Type expr: Constructor: four
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Even_ssucc
                            └──Constructor argument type:
                               └──Type expr: Constructor: even
                                  └──Type expr: Constructor: two
                            └──Constructor type:
                               └──Type expr: Constructor: even
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Constructor: two
                         └──Expression:
                            └──Type expr: Constructor: even
                               └──Type expr: Constructor: two
                            └──Desc: Variable
                               └──Variable: even2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: plus
                      └──Type expr: Constructor: two
                      └──Type expr: Constructor: one
                      └──Type expr: Constructor: three
                   └──Desc: Variable: p1
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: plus
                         └──Type expr: Constructor: two
                         └──Type expr: Constructor: one
                         └──Type expr: Constructor: three
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Plus_succ
                            └──Constructor argument type:
                               └──Type expr: Constructor: plus
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Constructor: zero
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Constructor: zero
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Constructor: zero
                            └──Constructor type:
                               └──Type expr: Constructor: plus
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Constructor: zero
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Constructor: zero
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Constructor: zero
                         └──Expression:
                            └──Type expr: Constructor: plus
                               └──Type expr: Constructor: succ
                                  └──Type expr: Constructor: zero
                               └──Type expr: Constructor: succ
                                  └──Type expr: Constructor: zero
                               └──Type expr: Constructor: succ
                                  └──Type expr: Constructor: succ
                                     └──Type expr: Constructor: zero
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Plus_succ
                                  └──Constructor argument type:
                                     └──Type expr: Constructor: plus
                                        └──Type expr: Constructor: zero
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Constructor: zero
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Constructor: zero
                                  └──Constructor type:
                                     └──Type expr: Constructor: plus
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Constructor: zero
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Constructor: zero
                                        └──Type expr: Constructor: succ
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Constructor: zero
                               └──Expression:
                                  └──Type expr: Constructor: plus
                                     └──Type expr: Constructor: zero
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Constructor: zero
                                     └──Type expr: Constructor: succ
                                        └──Type expr: Constructor: zero
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Plus_zero
                                        └──Constructor argument type:
                                           └──Type expr: Constructor: nat
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Constructor: zero
                                        └──Constructor type:
                                           └──Type expr: Constructor: plus
                                              └──Type expr: Constructor: zero
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Constructor: zero
                                              └──Type expr: Constructor: succ
                                                 └──Type expr: Constructor: zero
                                     └──Expression:
                                        └──Type expr: Constructor: nat
                                           └──Type expr: Constructor: succ
                                              └──Type expr: Constructor: zero
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: nat
                                                    └──Type expr: Constructor: zero
                                              └──Constructor type:
                                                 └──Type expr: Constructor: nat
                                                    └──Type expr: Constructor: succ
                                                       └──Type expr: Constructor: zero
                                           └──Expression:
                                              └──Type expr: Constructor: nat
                                                 └──Type expr: Constructor: zero
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Zero
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: nat
                                                          └──Type expr: Constructor: zero
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: summand_less_than_sum
                └──Abstraction:
                   └──Variables: a5924,a5923,a5922
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: plus
                            └──Type expr: Variable: a5950
                            └──Type expr: Variable: a5951
                            └──Type expr: Variable: a5952
                         └──Type expr: Constructor: le
                            └──Type expr: Variable: a5950
                            └──Type expr: Variable: a5952
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: plus
                               └──Type expr: Variable: a5950
                               └──Type expr: Variable: a5951
                               └──Type expr: Variable: a5952
                            └──Desc: Variable: p
                         └──Expression:
                            └──Type expr: Constructor: le
                               └──Type expr: Variable: a5950
                               └──Type expr: Variable: a5952
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: plus
                                     └──Type expr: Variable: a5950
                                     └──Type expr: Variable: a5951
                                     └──Type expr: Variable: a5952
                                  └──Desc: Variable
                                     └──Variable: p
                               └──Type expr: Constructor: plus
                                  └──Type expr: Variable: a5950
                                  └──Type expr: Variable: a5951
                                  └──Type expr: Variable: a5952
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: plus
                                           └──Type expr: Variable: a5950
                                           └──Type expr: Variable: a5951
                                           └──Type expr: Variable: a5952
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Plus_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: plus
                                                    └──Type expr: Variable: a5972
                                                    └──Type expr: Variable: a5951
                                                    └──Type expr: Variable: a5973
                                              └──Constructor type:
                                                 └──Type expr: Constructor: plus
                                                    └──Type expr: Variable: a5950
                                                    └──Type expr: Variable: a5951
                                                    └──Type expr: Variable: a5952
                                           └──Pattern:
                                              └──Type expr: Constructor: plus
                                                 └──Type expr: Variable: a5972
                                                 └──Type expr: Variable: a5951
                                                 └──Type expr: Variable: a5973
                                              └──Desc: Variable: p
                                     └──Expression:
                                        └──Type expr: Constructor: le
                                           └──Type expr: Variable: a5950
                                           └──Type expr: Variable: a5952
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Le_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: le
                                                    └──Type expr: Variable: a5972
                                                    └──Type expr: Variable: a5973
                                              └──Constructor type:
                                                 └──Type expr: Constructor: le
                                                    └──Type expr: Variable: a5950
                                                    └──Type expr: Variable: a5952
                                           └──Expression:
                                              └──Type expr: Constructor: le
                                                 └──Type expr: Variable: a5972
                                                 └──Type expr: Variable: a5973
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: plus
                                                          └──Type expr: Variable: a5972
                                                          └──Type expr: Variable: a5951
                                                          └──Type expr: Variable: a5973
                                                       └──Type expr: Constructor: le
                                                          └──Type expr: Variable: a5972
                                                          └──Type expr: Variable: a5973
                                                    └──Desc: Variable
                                                       └──Variable: summand_less_than_sum
                                                       └──Type expr: Variable: a5973
                                                       └──Type expr: Variable: a5951
                                                       └──Type expr: Variable: a5972
                                                 └──Expression:
                                                    └──Type expr: Constructor: plus
                                                       └──Type expr: Variable: a5972
                                                       └──Type expr: Variable: a5951
                                                       └──Type expr: Variable: a5973
                                                    └──Desc: Variable
                                                       └──Variable: p
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: plus
                                           └──Type expr: Variable: a5950
                                           └──Type expr: Variable: a5951
                                           └──Type expr: Variable: a5952
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Plus_zero
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: nat
                                                    └──Type expr: Variable: a5951
                                              └──Constructor type:
                                                 └──Type expr: Constructor: plus
                                                    └──Type expr: Variable: a5950
                                                    └──Type expr: Variable: a5951
                                                    └──Type expr: Variable: a5952
                                           └──Pattern:
                                              └──Type expr: Constructor: nat
                                                 └──Type expr: Variable: a5951
                                              └──Desc: Variable: n
                                     └──Expression:
                                        └──Type expr: Constructor: le
                                           └──Type expr: Variable: a5950
                                           └──Type expr: Variable: a5952
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Le_zero
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: nat
                                                    └──Type expr: Variable: a5951
                                              └──Constructor type:
                                                 └──Type expr: Constructor: le
                                                    └──Type expr: Constructor: zero
                                                    └──Type expr: Variable: a5951
                                           └──Expression:
                                              └──Type expr: Constructor: nat
                                                 └──Type expr: Variable: a5951
                                              └──Desc: Variable
                                                 └──Variable: n |}]

