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
                └──Variables: 19076
                └──Type expr: Variable: 19076
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
                   └──Constructor alphas: 18958
                   └──Constructor type:
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: 18958
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: 18958
       └──Structure item: Type
          └──Type declaration:
             └──Type name: nat
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Zero
                   └──Constructor alphas: 18960
                   └──Constructor type:
                      └──Type expr: Constructor: nat
                         └──Type expr: Variable: 18960
                   └──Constraint:
                      └──Type expr: Variable: 18960
                      └──Type expr: Constructor: zero
                └──Constructor declaration:
                   └──Constructor name: Succ
                   └──Constructor alphas: 18960
                   └──Constructor type:
                      └──Type expr: Constructor: nat
                         └──Type expr: Variable: 18960
                   └──Constructor argument:
                      └──Constructor betas: 18963
                      └──Type expr: Constructor: nat
                         └──Type expr: Variable: 18963
                   └──Constraint:
                      └──Type expr: Variable: 18960
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: 18963
       └──Structure item: Type
          └──Type declaration:
             └──Type name: seq
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: 18967 18968
                   └──Constructor type:
                      └──Type expr: Constructor: seq
                         └──Type expr: Variable: 18967
                         └──Type expr: Variable: 18968
                   └──Constraint:
                      └──Type expr: Variable: 18968
                      └──Type expr: Constructor: zero
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 18967 18968
                   └──Constructor type:
                      └──Type expr: Constructor: seq
                         └──Type expr: Variable: 18967
                         └──Type expr: Variable: 18968
                   └──Constructor argument:
                      └──Constructor betas: 18971
                      └──Type expr: Tuple
                         └──Type expr: Variable: 18967
                         └──Type expr: Constructor: seq
                            └──Type expr: Variable: 18967
                            └──Type expr: Variable: 18971
                   └──Constraint:
                      └──Type expr: Variable: 18968
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: 18971
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
                   └──Constructor alphas: 18976 18977 18978
                   └──Constructor type:
                      └──Type expr: Constructor: plus
                         └──Type expr: Variable: 18976
                         └──Type expr: Variable: 18977
                         └──Type expr: Variable: 18978
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: nat
                         └──Type expr: Variable: 18977
                   └──Constraint:
                      └──Type expr: Variable: 18976
                      └──Type expr: Constructor: zero
                   └──Constraint:
                      └──Type expr: Variable: 18977
                      └──Type expr: Variable: 18978
                └──Constructor declaration:
                   └──Constructor name: Plus_succ
                   └──Constructor alphas: 18976 18977 18978
                   └──Constructor type:
                      └──Type expr: Constructor: plus
                         └──Type expr: Variable: 18976
                         └──Type expr: Variable: 18977
                         └──Type expr: Variable: 18978
                   └──Constructor argument:
                      └──Constructor betas: 18983 18982
                      └──Type expr: Constructor: plus
                         └──Type expr: Variable: 18982
                         └──Type expr: Variable: 18977
                         └──Type expr: Variable: 18983
                   └──Constraint:
                      └──Type expr: Variable: 18976
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: 18982
                   └──Constraint:
                      └──Type expr: Variable: 18978
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: 18983
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: length
                └──Abstraction:
                   └──Variables: 19125,19124
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: seq
                            └──Type expr: Variable: 19147
                            └──Type expr: Variable: 19148
                         └──Type expr: Constructor: nat
                            └──Type expr: Variable: 19148
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: seq
                               └──Type expr: Variable: 19147
                               └──Type expr: Variable: 19148
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: nat
                               └──Type expr: Variable: 19148
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: seq
                                     └──Type expr: Variable: 19147
                                     └──Type expr: Variable: 19148
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: seq
                                  └──Type expr: Variable: 19147
                                  └──Type expr: Variable: 19148
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: seq
                                           └──Type expr: Variable: 19147
                                           └──Type expr: Variable: 19148
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Nil
                                              └──Constructor type:
                                                 └──Type expr: Constructor: seq
                                                    └──Type expr: Variable: 19147
                                                    └──Type expr: Variable: 19148
                                     └──Expression:
                                        └──Type expr: Constructor: nat
                                           └──Type expr: Variable: 19148
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Zero
                                              └──Constructor type:
                                                 └──Type expr: Constructor: nat
                                                    └──Type expr: Variable: 19148
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: seq
                                           └──Type expr: Variable: 19147
                                           └──Type expr: Variable: 19148
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Cons
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 19147
                                                    └──Type expr: Constructor: seq
                                                       └──Type expr: Variable: 19147
                                                       └──Type expr: Variable: 19185
                                              └──Constructor type:
                                                 └──Type expr: Constructor: seq
                                                    └──Type expr: Variable: 19147
                                                    └──Type expr: Variable: 19148
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: 19147
                                                 └──Type expr: Constructor: seq
                                                    └──Type expr: Variable: 19147
                                                    └──Type expr: Variable: 19185
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Variable: 19147
                                                    └──Desc: Any
                                                 └──Pattern:
                                                    └──Type expr: Constructor: seq
                                                       └──Type expr: Variable: 19147
                                                       └──Type expr: Variable: 19185
                                                    └──Desc: Variable: t
                                     └──Expression:
                                        └──Type expr: Constructor: nat
                                           └──Type expr: Variable: 19148
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: nat
                                                    └──Type expr: Variable: 19185
                                              └──Constructor type:
                                                 └──Type expr: Constructor: nat
                                                    └──Type expr: Variable: 19148
                                           └──Expression:
                                              └──Type expr: Constructor: nat
                                                 └──Type expr: Variable: 19185
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: seq
                                                          └──Type expr: Variable: 19147
                                                          └──Type expr: Variable: 19185
                                                       └──Type expr: Constructor: nat
                                                          └──Type expr: Variable: 19185
                                                    └──Desc: Variable
                                                       └──Variable: length
                                                       └──Type expr: Variable: 19185
                                                       └──Type expr: Variable: 19147
                                                 └──Expression:
                                                    └──Type expr: Constructor: seq
                                                       └──Type expr: Variable: 19147
                                                       └──Type expr: Variable: 19185
                                                    └──Desc: Variable
                                                       └──Variable: t
       └──Structure item: Type
          └──Type declaration:
             └──Type name: app
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: App
                   └──Constructor alphas: 18988 18989 18990
                   └──Constructor type:
                      └──Type expr: Constructor: app
                         └──Type expr: Variable: 18988
                         └──Type expr: Variable: 18989
                         └──Type expr: Variable: 18990
                   └──Constructor argument:
                      └──Constructor betas: 18991
                      └──Type expr: Tuple
                         └──Type expr: Constructor: seq
                            └──Type expr: Variable: 18988
                            └──Type expr: Variable: 18991
                         └──Type expr: Constructor: plus
                            └──Type expr: Variable: 18989
                            └──Type expr: Variable: 18990
                            └──Type expr: Variable: 18991
       └──Structure item: Primitive
          └──Value description:
             └──Name: hole
             └──Scheme:
                └──Variables: 19220
                └──Type expr: Variable: 19220
             └──Primitive name: %hole
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: append
                └──Abstraction:
                   └──Variables: 19233,19236,19235
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: seq
                            └──Type expr: Variable: 19267
                            └──Type expr: Variable: 19268
                         └──Type expr: Arrow
                            └──Type expr: Constructor: seq
                               └──Type expr: Variable: 19267
                               └──Type expr: Variable: 19280
                            └──Type expr: Constructor: app
                               └──Type expr: Variable: 19267
                               └──Type expr: Variable: 19268
                               └──Type expr: Variable: 19280
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: seq
                               └──Type expr: Variable: 19267
                               └──Type expr: Variable: 19268
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: seq
                                  └──Type expr: Variable: 19267
                                  └──Type expr: Variable: 19280
                               └──Type expr: Constructor: app
                                  └──Type expr: Variable: 19267
                                  └──Type expr: Variable: 19268
                                  └──Type expr: Variable: 19280
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: seq
                                     └──Type expr: Variable: 19267
                                     └──Type expr: Variable: 19280
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Constructor: app
                                     └──Type expr: Variable: 19267
                                     └──Type expr: Variable: 19268
                                     └──Type expr: Variable: 19280
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: seq
                                           └──Type expr: Variable: 19267
                                           └──Type expr: Variable: 19268
                                        └──Desc: Variable
                                           └──Variable: t1
                                     └──Type expr: Constructor: seq
                                        └──Type expr: Variable: 19267
                                        └──Type expr: Variable: 19268
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: seq
                                                 └──Type expr: Variable: 19267
                                                 └──Type expr: Variable: 19268
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: seq
                                                          └──Type expr: Variable: 19267
                                                          └──Type expr: Variable: 19268
                                           └──Expression:
                                              └──Type expr: Constructor: app
                                                 └──Type expr: Variable: 19267
                                                 └──Type expr: Variable: 19268
                                                 └──Type expr: Variable: 19280
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: App
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: seq
                                                             └──Type expr: Variable: 19267
                                                             └──Type expr: Variable: 19280
                                                          └──Type expr: Constructor: plus
                                                             └──Type expr: Variable: 19268
                                                             └──Type expr: Variable: 19280
                                                             └──Type expr: Variable: 19280
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: app
                                                          └──Type expr: Variable: 19267
                                                          └──Type expr: Variable: 19268
                                                          └──Type expr: Variable: 19280
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: seq
                                                          └──Type expr: Variable: 19267
                                                          └──Type expr: Variable: 19280
                                                       └──Type expr: Constructor: plus
                                                          └──Type expr: Variable: 19268
                                                          └──Type expr: Variable: 19280
                                                          └──Type expr: Variable: 19280
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: seq
                                                             └──Type expr: Variable: 19267
                                                             └──Type expr: Variable: 19280
                                                          └──Desc: Variable
                                                             └──Variable: t2
                                                       └──Expression:
                                                          └──Type expr: Constructor: plus
                                                             └──Type expr: Variable: 19268
                                                             └──Type expr: Variable: 19280
                                                             └──Type expr: Variable: 19280
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Plus_zero
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: nat
                                                                      └──Type expr: Variable: 19280
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: plus
                                                                      └──Type expr: Variable: 19268
                                                                      └──Type expr: Variable: 19280
                                                                      └──Type expr: Variable: 19280
                                                             └──Expression:
                                                                └──Type expr: Constructor: nat
                                                                   └──Type expr: Variable: 19280
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: seq
                                                                            └──Type expr: Variable: 19267
                                                                            └──Type expr: Variable: 19280
                                                                         └──Type expr: Constructor: nat
                                                                            └──Type expr: Variable: 19280
                                                                      └──Desc: Variable
                                                                         └──Variable: length
                                                                         └──Type expr: Variable: 19280
                                                                         └──Type expr: Variable: 19267
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: seq
                                                                         └──Type expr: Variable: 19267
                                                                         └──Type expr: Variable: 19280
                                                                      └──Desc: Variable
                                                                         └──Variable: t2
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: seq
                                                 └──Type expr: Variable: 19267
                                                 └──Type expr: Variable: 19268
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 19267
                                                          └──Type expr: Constructor: seq
                                                             └──Type expr: Variable: 19267
                                                             └──Type expr: Variable: 19359
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: seq
                                                          └──Type expr: Variable: 19267
                                                          └──Type expr: Variable: 19268
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 19267
                                                       └──Type expr: Constructor: seq
                                                          └──Type expr: Variable: 19267
                                                          └──Type expr: Variable: 19359
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Variable: 19267
                                                          └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: seq
                                                             └──Type expr: Variable: 19267
                                                             └──Type expr: Variable: 19359
                                                          └──Desc: Variable: t1
                                           └──Expression:
                                              └──Type expr: Constructor: app
                                                 └──Type expr: Variable: 19267
                                                 └──Type expr: Variable: 19268
                                                 └──Type expr: Variable: 19280
                                              └──Desc: Match
                                                 └──Expression:
                                                    └──Type expr: Constructor: app
                                                       └──Type expr: Variable: 19267
                                                       └──Type expr: Variable: 19359
                                                       └──Type expr: Variable: 19280
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: seq
                                                                └──Type expr: Variable: 19267
                                                                └──Type expr: Variable: 19280
                                                             └──Type expr: Constructor: app
                                                                └──Type expr: Variable: 19267
                                                                └──Type expr: Variable: 19359
                                                                └──Type expr: Variable: 19280
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: seq
                                                                      └──Type expr: Variable: 19267
                                                                      └──Type expr: Variable: 19359
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: seq
                                                                         └──Type expr: Variable: 19267
                                                                         └──Type expr: Variable: 19280
                                                                      └──Type expr: Constructor: app
                                                                         └──Type expr: Variable: 19267
                                                                         └──Type expr: Variable: 19359
                                                                         └──Type expr: Variable: 19280
                                                                └──Desc: Variable
                                                                   └──Variable: append
                                                                   └──Type expr: Variable: 19280
                                                                   └──Type expr: Variable: 19359
                                                                   └──Type expr: Variable: 19267
                                                             └──Expression:
                                                                └──Type expr: Constructor: seq
                                                                   └──Type expr: Variable: 19267
                                                                   └──Type expr: Variable: 19359
                                                                └──Desc: Variable
                                                                   └──Variable: t1
                                                       └──Expression:
                                                          └──Type expr: Constructor: seq
                                                             └──Type expr: Variable: 19267
                                                             └──Type expr: Variable: 19280
                                                          └──Desc: Variable
                                                             └──Variable: t2
                                                 └──Type expr: Constructor: app
                                                    └──Type expr: Variable: 19267
                                                    └──Type expr: Variable: 19359
                                                    └──Type expr: Variable: 19280
                                                 └──Cases:
                                                    └──Case:
                                                       └──Pattern:
                                                          └──Type expr: Constructor: app
                                                             └──Type expr: Variable: 19267
                                                             └──Type expr: Variable: 19359
                                                             └──Type expr: Variable: 19280
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: App
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: seq
                                                                         └──Type expr: Variable: 19267
                                                                         └──Type expr: Variable: 19406
                                                                      └──Type expr: Constructor: plus
                                                                         └──Type expr: Variable: 19359
                                                                         └──Type expr: Variable: 19280
                                                                         └──Type expr: Variable: 19406
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: app
                                                                      └──Type expr: Variable: 19267
                                                                      └──Type expr: Variable: 19359
                                                                      └──Type expr: Variable: 19280
                                                             └──Pattern:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: seq
                                                                      └──Type expr: Variable: 19267
                                                                      └──Type expr: Variable: 19406
                                                                   └──Type expr: Constructor: plus
                                                                      └──Type expr: Variable: 19359
                                                                      └──Type expr: Variable: 19280
                                                                      └──Type expr: Variable: 19406
                                                                └──Desc: Tuple
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: seq
                                                                         └──Type expr: Variable: 19267
                                                                         └──Type expr: Variable: 19406
                                                                      └──Desc: Variable: t1
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: plus
                                                                         └──Type expr: Variable: 19359
                                                                         └──Type expr: Variable: 19280
                                                                         └──Type expr: Variable: 19406
                                                                      └──Desc: Variable: plus
                                                       └──Expression:
                                                          └──Type expr: Constructor: app
                                                             └──Type expr: Variable: 19267
                                                             └──Type expr: Variable: 19268
                                                             └──Type expr: Variable: 19280
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: App
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: seq
                                                                         └──Type expr: Variable: 19267
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: 19406
                                                                      └──Type expr: Constructor: plus
                                                                         └──Type expr: Variable: 19268
                                                                         └──Type expr: Variable: 19280
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: 19406
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: app
                                                                      └──Type expr: Variable: 19267
                                                                      └──Type expr: Variable: 19268
                                                                      └──Type expr: Variable: 19280
                                                             └──Expression:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: seq
                                                                      └──Type expr: Variable: 19267
                                                                      └──Type expr: Constructor: succ
                                                                         └──Type expr: Variable: 19406
                                                                   └──Type expr: Constructor: plus
                                                                      └──Type expr: Variable: 19268
                                                                      └──Type expr: Variable: 19280
                                                                      └──Type expr: Constructor: succ
                                                                         └──Type expr: Variable: 19406
                                                                └──Desc: Tuple
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: seq
                                                                         └──Type expr: Variable: 19267
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: 19406
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Cons
                                                                            └──Constructor argument type:
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: 19267
                                                                                  └──Type expr: Constructor: seq
                                                                                     └──Type expr: Variable: 19267
                                                                                     └──Type expr: Variable: 19406
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: seq
                                                                                  └──Type expr: Variable: 19267
                                                                                  └──Type expr: Constructor: succ
                                                                                     └──Type expr: Variable: 19406
                                                                         └──Expression:
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 19267
                                                                               └──Type expr: Constructor: seq
                                                                                  └──Type expr: Variable: 19267
                                                                                  └──Type expr: Variable: 19406
                                                                            └──Desc: Tuple
                                                                               └──Expression:
                                                                                  └──Type expr: Variable: 19267
                                                                                  └──Desc: Variable
                                                                                     └──Variable: x
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: seq
                                                                                     └──Type expr: Variable: 19267
                                                                                     └──Type expr: Variable: 19406
                                                                                  └──Desc: Variable
                                                                                     └──Variable: t1
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: plus
                                                                         └──Type expr: Variable: 19268
                                                                         └──Type expr: Variable: 19280
                                                                         └──Type expr: Constructor: succ
                                                                            └──Type expr: Variable: 19406
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Plus_succ
                                                                            └──Constructor argument type:
                                                                               └──Type expr: Constructor: plus
                                                                                  └──Type expr: Variable: 19359
                                                                                  └──Type expr: Variable: 19280
                                                                                  └──Type expr: Variable: 19406
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: plus
                                                                                  └──Type expr: Variable: 19268
                                                                                  └──Type expr: Variable: 19280
                                                                                  └──Type expr: Constructor: succ
                                                                                     └──Type expr: Variable: 19406
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: plus
                                                                               └──Type expr: Variable: 19359
                                                                               └──Type expr: Variable: 19280
                                                                               └──Type expr: Variable: 19406
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
                   └──Constructor alphas: 18998
                   └──Constructor type:
                      └──Type expr: Constructor: shape
                         └──Type expr: Variable: 18998
                   └──Constraint:
                      └──Type expr: Variable: 18998
                      └──Type expr: Constructor: tp
                └──Constructor declaration:
                   └──Constructor name: Node
                   └──Constructor alphas: 18998
                   └──Constructor type:
                      └──Type expr: Constructor: shape
                         └──Type expr: Variable: 18998
                   └──Constraint:
                      └──Type expr: Variable: 18998
                      └──Type expr: Constructor: nd
                └──Constructor declaration:
                   └──Constructor name: Fork
                   └──Constructor alphas: 18998
                   └──Constructor type:
                      └──Type expr: Constructor: shape
                         └──Type expr: Variable: 18998
                   └──Constructor argument:
                      └──Constructor betas: 19004 19003
                      └──Type expr: Tuple
                         └──Type expr: Constructor: shape
                            └──Type expr: Variable: 19003
                         └──Type expr: Constructor: shape
                            └──Type expr: Variable: 19004
                   └──Constraint:
                      └──Type expr: Variable: 18998
                      └──Type expr: Constructor: fk
                         └──Type expr: Variable: 19003
                         └──Type expr: Variable: 19004
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
                   └──Constructor alphas: 19010
                   └──Constructor type:
                      └──Type expr: Constructor: boolean
                         └──Type expr: Variable: 19010
                   └──Constraint:
                      └──Type expr: Variable: 19010
                      └──Type expr: Constructor: tt
                └──Constructor declaration:
                   └──Constructor name: Bool_false
                   └──Constructor alphas: 19010
                   └──Constructor type:
                      └──Type expr: Constructor: boolean
                         └──Type expr: Variable: 19010
                   └──Constraint:
                      └──Type expr: Variable: 19010
                      └──Type expr: Constructor: ff
       └──Structure item: Type
          └──Type declaration:
             └──Type name: path
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Path_none
                   └──Constructor alphas: 19015 19016
                   └──Constructor type:
                      └──Type expr: Constructor: path
                         └──Type expr: Variable: 19015
                         └──Type expr: Variable: 19016
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: 19016
                   └──Constraint:
                      └──Type expr: Variable: 19015
                      └──Type expr: Constructor: tp
                └──Constructor declaration:
                   └──Constructor name: Path_here
                   └──Constructor alphas: 19015 19016
                   └──Constructor type:
                      └──Type expr: Constructor: path
                         └──Type expr: Variable: 19015
                         └──Type expr: Variable: 19016
                   └──Constraint:
                      └──Type expr: Variable: 19015
                      └──Type expr: Constructor: nd
                └──Constructor declaration:
                   └──Constructor name: Path_left
                   └──Constructor alphas: 19015 19016
                   └──Constructor type:
                      └──Type expr: Constructor: path
                         └──Type expr: Variable: 19015
                         └──Type expr: Variable: 19016
                   └──Constructor argument:
                      └──Constructor betas: 19022 19021
                      └──Type expr: Constructor: path
                         └──Type expr: Variable: 19021
                         └──Type expr: Variable: 19016
                   └──Constraint:
                      └──Type expr: Variable: 19015
                      └──Type expr: Constructor: fk
                         └──Type expr: Variable: 19021
                         └──Type expr: Variable: 19022
                └──Constructor declaration:
                   └──Constructor name: Path_right
                   └──Constructor alphas: 19015 19016
                   └──Constructor type:
                      └──Type expr: Constructor: path
                         └──Type expr: Variable: 19015
                         └──Type expr: Variable: 19016
                   └──Constructor argument:
                      └──Constructor betas: 19027 19026
                      └──Type expr: Constructor: path
                         └──Type expr: Variable: 19027
                         └──Type expr: Variable: 19016
                   └──Constraint:
                      └──Type expr: Variable: 19015
                      └──Type expr: Constructor: fk
                         └──Type expr: Variable: 19026
                         └──Type expr: Variable: 19027
       └──Structure item: Type
          └──Type declaration:
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: 19031
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 19031
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 19031
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 19031
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: 19031
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 19031
       └──Structure item: Primitive
          └──Value description:
             └──Name: map
             └──Scheme:
                └──Variables: 19478,19477
                └──Type expr: Arrow
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: 19477
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: 19477
                         └──Type expr: Variable: 19478
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 19478
             └──Primitive name: %map
       └──Structure item: Type
          └──Type declaration:
             └──Type name: tree
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Tree_tip
                   └──Constructor alphas: 19036 19037
                   └──Constructor type:
                      └──Type expr: Constructor: tree
                         └──Type expr: Variable: 19036
                         └──Type expr: Variable: 19037
                   └──Constraint:
                      └──Type expr: Variable: 19036
                      └──Type expr: Constructor: tp
                └──Constructor declaration:
                   └──Constructor name: Tree_node
                   └──Constructor alphas: 19036 19037
                   └──Constructor type:
                      └──Type expr: Constructor: tree
                         └──Type expr: Variable: 19036
                         └──Type expr: Variable: 19037
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: 19037
                   └──Constraint:
                      └──Type expr: Variable: 19036
                      └──Type expr: Constructor: nd
                └──Constructor declaration:
                   └──Constructor name: Tree_fork
                   └──Constructor alphas: 19036 19037
                   └──Constructor type:
                      └──Type expr: Constructor: tree
                         └──Type expr: Variable: 19036
                         └──Type expr: Variable: 19037
                   └──Constructor argument:
                      └──Constructor betas: 19043 19042
                      └──Type expr: Tuple
                         └──Type expr: Constructor: tree
                            └──Type expr: Variable: 19042
                            └──Type expr: Variable: 19037
                         └──Type expr: Constructor: tree
                            └──Type expr: Variable: 19043
                            └──Type expr: Variable: 19037
                   └──Constraint:
                      └──Type expr: Variable: 19036
                      └──Type expr: Constructor: fk
                         └──Type expr: Variable: 19042
                         └──Type expr: Variable: 19043
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
                   └──Variables: 19598
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 19598
                         └──Type expr: Arrow
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: 19598
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: 19598
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: 19598
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: 19598
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: 19598
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: 19598
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: 19598
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Variable: 19598
                                        └──Desc: Variable
                                           └──Variable: t1
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: 19598
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: 19598
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: 19598
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: 19598
                                              └──Desc: Variable
                                                 └──Variable: t2
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: 19598
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 19598
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: 19598
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: 19598
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 19598
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: 19598
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Variable: 19598
                                                          └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: 19598
                                                          └──Desc: Variable: t
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: 19598
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 19598
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: 19598
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: 19598
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 19598
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: 19598
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Variable: 19598
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: 19598
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: 19598
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: 19598
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Variable: 19598
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: 19598
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: 19598
                                                                      └──Desc: Variable
                                                                         └──Variable: app
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Variable: 19598
                                                                      └──Desc: Variable
                                                                         └──Variable: t1
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: 19598
                                                                └──Desc: Variable
                                                                   └──Variable: t2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: find
                └──Abstraction:
                   └──Variables: 19632,19637
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: 19684
                            └──Type expr: Arrow
                               └──Type expr: Variable: 19684
                               └──Type expr: Constructor: bool
                         └──Type expr: Arrow
                            └──Type expr: Variable: 19684
                            └──Type expr: Arrow
                               └──Type expr: Constructor: tree
                                  └──Type expr: Variable: 19702
                                  └──Type expr: Variable: 19684
                               └──Type expr: Constructor: list
                                  └──Type expr: Constructor: path
                                     └──Type expr: Variable: 19702
                                     └──Type expr: Variable: 19684
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Variable: 19684
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 19684
                                  └──Type expr: Constructor: bool
                            └──Desc: Variable: eq
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: 19684
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: tree
                                     └──Type expr: Variable: 19702
                                     └──Type expr: Variable: 19684
                                  └──Type expr: Constructor: list
                                     └──Type expr: Constructor: path
                                        └──Type expr: Variable: 19702
                                        └──Type expr: Variable: 19684
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: 19684
                                  └──Desc: Variable: n
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: tree
                                        └──Type expr: Variable: 19702
                                        └──Type expr: Variable: 19684
                                     └──Type expr: Constructor: list
                                        └──Type expr: Constructor: path
                                           └──Type expr: Variable: 19702
                                           └──Type expr: Variable: 19684
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: tree
                                           └──Type expr: Variable: 19702
                                           └──Type expr: Variable: 19684
                                        └──Desc: Variable: t
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Constructor: path
                                              └──Type expr: Variable: 19702
                                              └──Type expr: Variable: 19684
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Variable: 19702
                                                 └──Type expr: Variable: 19684
                                              └──Desc: Variable
                                                 └──Variable: t
                                           └──Type expr: Constructor: tree
                                              └──Type expr: Variable: 19702
                                              └──Type expr: Variable: 19684
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: 19702
                                                       └──Type expr: Variable: 19684
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Tree_tip
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: 19702
                                                                └──Type expr: Variable: 19684
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: path
                                                          └──Type expr: Variable: 19702
                                                          └──Type expr: Variable: 19684
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Nil
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: path
                                                                   └──Type expr: Variable: 19702
                                                                   └──Type expr: Variable: 19684
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: 19702
                                                       └──Type expr: Variable: 19684
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Tree_node
                                                          └──Constructor argument type:
                                                             └──Type expr: Variable: 19684
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: 19702
                                                                └──Type expr: Variable: 19684
                                                       └──Pattern:
                                                          └──Type expr: Variable: 19684
                                                          └──Desc: Variable: m
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: path
                                                          └──Type expr: Variable: 19702
                                                          └──Type expr: Variable: 19684
                                                    └──Desc: If
                                                       └──Expression:
                                                          └──Type expr: Constructor: bool
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: 19684
                                                                   └──Type expr: Constructor: bool
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: 19684
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Variable: 19684
                                                                            └──Type expr: Constructor: bool
                                                                      └──Desc: Variable
                                                                         └──Variable: eq
                                                                   └──Expression:
                                                                      └──Type expr: Variable: 19684
                                                                      └──Desc: Variable
                                                                         └──Variable: n
                                                             └──Expression:
                                                                └──Type expr: Variable: 19684
                                                                └──Desc: Variable
                                                                   └──Variable: m
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: path
                                                                └──Type expr: Variable: 19702
                                                                └──Type expr: Variable: 19684
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Cons
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: path
                                                                         └──Type expr: Variable: 19702
                                                                         └──Type expr: Variable: 19684
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: path
                                                                            └──Type expr: Variable: 19702
                                                                            └──Type expr: Variable: 19684
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: path
                                                                         └──Type expr: Variable: 19702
                                                                         └──Type expr: Variable: 19684
                                                             └──Expression:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: path
                                                                      └──Type expr: Variable: 19702
                                                                      └──Type expr: Variable: 19684
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: path
                                                                         └──Type expr: Variable: 19702
                                                                         └──Type expr: Variable: 19684
                                                                └──Desc: Tuple
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: path
                                                                         └──Type expr: Variable: 19702
                                                                         └──Type expr: Variable: 19684
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Path_here
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: path
                                                                                  └──Type expr: Variable: 19702
                                                                                  └──Type expr: Variable: 19684
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: path
                                                                            └──Type expr: Variable: 19702
                                                                            └──Type expr: Variable: 19684
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Nil
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: path
                                                                                     └──Type expr: Variable: 19702
                                                                                     └──Type expr: Variable: 19684
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: path
                                                                └──Type expr: Variable: 19702
                                                                └──Type expr: Variable: 19684
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Nil
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: path
                                                                         └──Type expr: Variable: 19702
                                                                         └──Type expr: Variable: 19684
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: 19702
                                                       └──Type expr: Variable: 19684
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Tree_fork
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: 19806
                                                                   └──Type expr: Variable: 19684
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: 19804
                                                                   └──Type expr: Variable: 19684
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: 19702
                                                                └──Type expr: Variable: 19684
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: 19806
                                                                └──Type expr: Variable: 19684
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: 19804
                                                                └──Type expr: Variable: 19684
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: 19806
                                                                   └──Type expr: Variable: 19684
                                                                └──Desc: Variable: l
                                                             └──Pattern:
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: 19804
                                                                   └──Type expr: Variable: 19684
                                                                └──Desc: Variable: r
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: path
                                                          └──Type expr: Variable: 19702
                                                          └──Type expr: Variable: 19684
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: path
                                                                   └──Type expr: Constructor: fk
                                                                      └──Type expr: Variable: 19806
                                                                      └──Type expr: Variable: 19804
                                                                   └──Type expr: Variable: 19684
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: path
                                                                   └──Type expr: Constructor: fk
                                                                      └──Type expr: Variable: 19806
                                                                      └──Type expr: Variable: 19804
                                                                   └──Type expr: Variable: 19684
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: path
                                                                         └──Type expr: Constructor: fk
                                                                            └──Type expr: Variable: 19806
                                                                            └──Type expr: Variable: 19804
                                                                         └──Type expr: Variable: 19684
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: path
                                                                            └──Type expr: Constructor: fk
                                                                               └──Type expr: Variable: 19806
                                                                               └──Type expr: Variable: 19804
                                                                            └──Type expr: Variable: 19684
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: path
                                                                            └──Type expr: Constructor: fk
                                                                               └──Type expr: Variable: 19806
                                                                               └──Type expr: Variable: 19804
                                                                            └──Type expr: Variable: 19684
                                                                └──Desc: Variable
                                                                   └──Variable: app
                                                                   └──Type expr: Constructor: path
                                                                      └──Type expr: Constructor: fk
                                                                         └──Type expr: Variable: 19806
                                                                         └──Type expr: Variable: 19804
                                                                      └──Type expr: Variable: 19684
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: path
                                                                      └──Type expr: Constructor: fk
                                                                         └──Type expr: Variable: 19806
                                                                         └──Type expr: Variable: 19804
                                                                      └──Type expr: Variable: 19684
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: path
                                                                               └──Type expr: Variable: 19806
                                                                               └──Type expr: Variable: 19684
                                                                            └──Type expr: Constructor: path
                                                                               └──Type expr: Constructor: fk
                                                                                  └──Type expr: Variable: 19806
                                                                                  └──Type expr: Variable: 19804
                                                                               └──Type expr: Variable: 19684
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: path
                                                                               └──Type expr: Constructor: fk
                                                                                  └──Type expr: Variable: 19806
                                                                                  └──Type expr: Variable: 19804
                                                                               └──Type expr: Variable: 19684
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: path
                                                                                     └──Type expr: Variable: 19806
                                                                                     └──Type expr: Variable: 19684
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: path
                                                                                        └──Type expr: Variable: 19806
                                                                                        └──Type expr: Variable: 19684
                                                                                     └──Type expr: Constructor: path
                                                                                        └──Type expr: Constructor: fk
                                                                                           └──Type expr: Variable: 19806
                                                                                           └──Type expr: Variable: 19804
                                                                                        └──Type expr: Variable: 19684
                                                                                  └──Type expr: Constructor: list
                                                                                     └──Type expr: Constructor: path
                                                                                        └──Type expr: Constructor: fk
                                                                                           └──Type expr: Variable: 19806
                                                                                           └──Type expr: Variable: 19804
                                                                                        └──Type expr: Variable: 19684
                                                                            └──Desc: Variable
                                                                               └──Variable: map
                                                                               └──Type expr: Constructor: path
                                                                                  └──Type expr: Constructor: fk
                                                                                     └──Type expr: Variable: 19806
                                                                                     └──Type expr: Variable: 19804
                                                                                  └──Type expr: Variable: 19684
                                                                               └──Type expr: Constructor: path
                                                                                  └──Type expr: Variable: 19806
                                                                                  └──Type expr: Variable: 19684
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: path
                                                                                  └──Type expr: Variable: 19806
                                                                                  └──Type expr: Variable: 19684
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: tree
                                                                                        └──Type expr: Variable: 19806
                                                                                        └──Type expr: Variable: 19684
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Constructor: path
                                                                                           └──Type expr: Variable: 19806
                                                                                           └──Type expr: Variable: 19684
                                                                                  └──Desc: Application
                                                                                     └──Expression:
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Variable: 19684
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Constructor: tree
                                                                                                 └──Type expr: Variable: 19806
                                                                                                 └──Type expr: Variable: 19684
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Constructor: path
                                                                                                    └──Type expr: Variable: 19806
                                                                                                    └──Type expr: Variable: 19684
                                                                                        └──Desc: Application
                                                                                           └──Expression:
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Variable: 19684
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Variable: 19684
                                                                                                       └──Type expr: Constructor: bool
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Variable: 19684
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Constructor: tree
                                                                                                          └──Type expr: Variable: 19806
                                                                                                          └──Type expr: Variable: 19684
                                                                                                       └──Type expr: Constructor: list
                                                                                                          └──Type expr: Constructor: path
                                                                                                             └──Type expr: Variable: 19806
                                                                                                             └──Type expr: Variable: 19684
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: find
                                                                                                 └──Type expr: Variable: 19806
                                                                                                 └──Type expr: Variable: 19684
                                                                                           └──Expression:
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Variable: 19684
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Variable: 19684
                                                                                                    └──Type expr: Constructor: bool
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: eq
                                                                                     └──Expression:
                                                                                        └──Type expr: Variable: 19684
                                                                                        └──Desc: Variable
                                                                                           └──Variable: n
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: tree
                                                                                     └──Type expr: Variable: 19806
                                                                                     └──Type expr: Variable: 19684
                                                                                  └──Desc: Variable
                                                                                     └──Variable: l
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: path
                                                                            └──Type expr: Variable: 19806
                                                                            └──Type expr: Variable: 19684
                                                                         └──Type expr: Constructor: path
                                                                            └──Type expr: Constructor: fk
                                                                               └──Type expr: Variable: 19806
                                                                               └──Type expr: Variable: 19804
                                                                            └──Type expr: Variable: 19684
                                                                      └──Desc: Function
                                                                         └──Pattern:
                                                                            └──Type expr: Constructor: path
                                                                               └──Type expr: Variable: 19806
                                                                               └──Type expr: Variable: 19684
                                                                            └──Desc: Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: path
                                                                               └──Type expr: Constructor: fk
                                                                                  └──Type expr: Variable: 19806
                                                                                  └──Type expr: Variable: 19804
                                                                               └──Type expr: Variable: 19684
                                                                            └──Desc: Construct
                                                                               └──Constructor description:
                                                                                  └──Name: Path_left
                                                                                  └──Constructor argument type:
                                                                                     └──Type expr: Constructor: path
                                                                                        └──Type expr: Variable: 19806
                                                                                        └──Type expr: Variable: 19684
                                                                                  └──Constructor type:
                                                                                     └──Type expr: Constructor: path
                                                                                        └──Type expr: Constructor: fk
                                                                                           └──Type expr: Variable: 19806
                                                                                           └──Type expr: Variable: 19804
                                                                                        └──Type expr: Variable: 19684
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: path
                                                                                     └──Type expr: Variable: 19806
                                                                                     └──Type expr: Variable: 19684
                                                                                  └──Desc: Variable
                                                                                     └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: path
                                                                └──Type expr: Constructor: fk
                                                                   └──Type expr: Variable: 19806
                                                                   └──Type expr: Variable: 19804
                                                                └──Type expr: Variable: 19684
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: path
                                                                         └──Type expr: Variable: 19804
                                                                         └──Type expr: Variable: 19684
                                                                      └──Type expr: Constructor: path
                                                                         └──Type expr: Constructor: fk
                                                                            └──Type expr: Variable: 19806
                                                                            └──Type expr: Variable: 19804
                                                                         └──Type expr: Variable: 19684
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: path
                                                                         └──Type expr: Constructor: fk
                                                                            └──Type expr: Variable: 19806
                                                                            └──Type expr: Variable: 19804
                                                                         └──Type expr: Variable: 19684
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: path
                                                                               └──Type expr: Variable: 19804
                                                                               └──Type expr: Variable: 19684
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: path
                                                                                  └──Type expr: Variable: 19804
                                                                                  └──Type expr: Variable: 19684
                                                                               └──Type expr: Constructor: path
                                                                                  └──Type expr: Constructor: fk
                                                                                     └──Type expr: Variable: 19806
                                                                                     └──Type expr: Variable: 19804
                                                                                  └──Type expr: Variable: 19684
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: path
                                                                                  └──Type expr: Constructor: fk
                                                                                     └──Type expr: Variable: 19806
                                                                                     └──Type expr: Variable: 19804
                                                                                  └──Type expr: Variable: 19684
                                                                      └──Desc: Variable
                                                                         └──Variable: map
                                                                         └──Type expr: Constructor: path
                                                                            └──Type expr: Constructor: fk
                                                                               └──Type expr: Variable: 19806
                                                                               └──Type expr: Variable: 19804
                                                                            └──Type expr: Variable: 19684
                                                                         └──Type expr: Constructor: path
                                                                            └──Type expr: Variable: 19804
                                                                            └──Type expr: Variable: 19684
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: path
                                                                            └──Type expr: Variable: 19804
                                                                            └──Type expr: Variable: 19684
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: tree
                                                                                  └──Type expr: Variable: 19804
                                                                                  └──Type expr: Variable: 19684
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: path
                                                                                     └──Type expr: Variable: 19804
                                                                                     └──Type expr: Variable: 19684
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Variable: 19684
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: tree
                                                                                           └──Type expr: Variable: 19804
                                                                                           └──Type expr: Variable: 19684
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Constructor: path
                                                                                              └──Type expr: Variable: 19804
                                                                                              └──Type expr: Variable: 19684
                                                                                  └──Desc: Application
                                                                                     └──Expression:
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Variable: 19684
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Variable: 19684
                                                                                                 └──Type expr: Constructor: bool
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Variable: 19684
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Constructor: tree
                                                                                                    └──Type expr: Variable: 19804
                                                                                                    └──Type expr: Variable: 19684
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: path
                                                                                                       └──Type expr: Variable: 19804
                                                                                                       └──Type expr: Variable: 19684
                                                                                        └──Desc: Variable
                                                                                           └──Variable: find
                                                                                           └──Type expr: Variable: 19804
                                                                                           └──Type expr: Variable: 19684
                                                                                     └──Expression:
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Variable: 19684
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Variable: 19684
                                                                                              └──Type expr: Constructor: bool
                                                                                        └──Desc: Variable
                                                                                           └──Variable: eq
                                                                               └──Expression:
                                                                                  └──Type expr: Variable: 19684
                                                                                  └──Desc: Variable
                                                                                     └──Variable: n
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: tree
                                                                               └──Type expr: Variable: 19804
                                                                               └──Type expr: Variable: 19684
                                                                            └──Desc: Variable
                                                                               └──Variable: r
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: path
                                                                      └──Type expr: Variable: 19804
                                                                      └──Type expr: Variable: 19684
                                                                   └──Type expr: Constructor: path
                                                                      └──Type expr: Constructor: fk
                                                                         └──Type expr: Variable: 19806
                                                                         └──Type expr: Variable: 19804
                                                                      └──Type expr: Variable: 19684
                                                                └──Desc: Function
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: path
                                                                         └──Type expr: Variable: 19804
                                                                         └──Type expr: Variable: 19684
                                                                      └──Desc: Variable: x
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: path
                                                                         └──Type expr: Constructor: fk
                                                                            └──Type expr: Variable: 19806
                                                                            └──Type expr: Variable: 19804
                                                                         └──Type expr: Variable: 19684
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Path_right
                                                                            └──Constructor argument type:
                                                                               └──Type expr: Constructor: path
                                                                                  └──Type expr: Variable: 19804
                                                                                  └──Type expr: Variable: 19684
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: path
                                                                                  └──Type expr: Constructor: fk
                                                                                     └──Type expr: Variable: 19806
                                                                                     └──Type expr: Variable: 19804
                                                                                  └──Type expr: Variable: 19684
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: path
                                                                               └──Type expr: Variable: 19804
                                                                               └──Type expr: Variable: 19684
                                                                            └──Desc: Variable
                                                                               └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: extract
                └──Abstraction:
                   └──Variables: 19981,19980
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: path
                            └──Type expr: Variable: 20007
                            └──Type expr: Variable: 20008
                         └──Type expr: Arrow
                            └──Type expr: Constructor: tree
                               └──Type expr: Variable: 20007
                               └──Type expr: Variable: 20008
                            └──Type expr: Variable: 20008
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: path
                               └──Type expr: Variable: 20007
                               └──Type expr: Variable: 20008
                            └──Desc: Variable: p
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: tree
                                  └──Type expr: Variable: 20007
                                  └──Type expr: Variable: 20008
                               └──Type expr: Variable: 20008
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: tree
                                     └──Type expr: Variable: 20007
                                     └──Type expr: Variable: 20008
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Variable: 20008
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: path
                                              └──Type expr: Variable: 20007
                                              └──Type expr: Variable: 20008
                                           └──Type expr: Constructor: tree
                                              └──Type expr: Variable: 20007
                                              └──Type expr: Variable: 20008
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: path
                                                 └──Type expr: Variable: 20007
                                                 └──Type expr: Variable: 20008
                                              └──Desc: Variable
                                                 └──Variable: p
                                           └──Expression:
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Variable: 20007
                                                 └──Type expr: Variable: 20008
                                              └──Desc: Variable
                                                 └──Variable: t
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: path
                                           └──Type expr: Variable: 20007
                                           └──Type expr: Variable: 20008
                                        └──Type expr: Constructor: tree
                                           └──Type expr: Variable: 20007
                                           └──Type expr: Variable: 20008
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: path
                                                    └──Type expr: Variable: 20007
                                                    └──Type expr: Variable: 20008
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: 20007
                                                    └──Type expr: Variable: 20008
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: path
                                                       └──Type expr: Variable: 20007
                                                       └──Type expr: Variable: 20008
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Path_none
                                                          └──Constructor argument type:
                                                             └──Type expr: Variable: 20008
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: path
                                                                └──Type expr: Variable: 20007
                                                                └──Type expr: Variable: 20008
                                                       └──Pattern:
                                                          └──Type expr: Variable: 20008
                                                          └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: 20007
                                                       └──Type expr: Variable: 20008
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Tree_tip
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: 20007
                                                                └──Type expr: Variable: 20008
                                           └──Expression:
                                              └──Type expr: Variable: 20008
                                              └──Desc: Variable
                                                 └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: path
                                                    └──Type expr: Variable: 20007
                                                    └──Type expr: Variable: 20008
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: 20007
                                                    └──Type expr: Variable: 20008
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: path
                                                       └──Type expr: Variable: 20007
                                                       └──Type expr: Variable: 20008
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Path_here
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: path
                                                                └──Type expr: Variable: 20007
                                                                └──Type expr: Variable: 20008
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: 20007
                                                       └──Type expr: Variable: 20008
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Tree_node
                                                          └──Constructor argument type:
                                                             └──Type expr: Variable: 20008
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: 20007
                                                                └──Type expr: Variable: 20008
                                                       └──Pattern:
                                                          └──Type expr: Variable: 20008
                                                          └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Variable: 20008
                                              └──Desc: Variable
                                                 └──Variable: y
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: path
                                                    └──Type expr: Variable: 20007
                                                    └──Type expr: Variable: 20008
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: 20007
                                                    └──Type expr: Variable: 20008
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: path
                                                       └──Type expr: Variable: 20007
                                                       └──Type expr: Variable: 20008
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Path_left
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: path
                                                                └──Type expr: Variable: 20086
                                                                └──Type expr: Variable: 20008
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: path
                                                                └──Type expr: Variable: 20007
                                                                └──Type expr: Variable: 20008
                                                       └──Pattern:
                                                          └──Type expr: Constructor: path
                                                             └──Type expr: Variable: 20086
                                                             └──Type expr: Variable: 20008
                                                          └──Desc: Variable: p
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: 20007
                                                       └──Type expr: Variable: 20008
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Tree_fork
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: 20083
                                                                   └──Type expr: Variable: 20008
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: 20081
                                                                   └──Type expr: Variable: 20008
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: 20007
                                                                └──Type expr: Variable: 20008
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: 20083
                                                                └──Type expr: Variable: 20008
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: 20081
                                                                └──Type expr: Variable: 20008
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: 20083
                                                                   └──Type expr: Variable: 20008
                                                                └──Desc: Variable: l
                                                             └──Pattern:
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: 20081
                                                                   └──Type expr: Variable: 20008
                                                                └──Desc: Any
                                           └──Expression:
                                              └──Type expr: Variable: 20008
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: 20083
                                                          └──Type expr: Variable: 20008
                                                       └──Type expr: Variable: 20008
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: path
                                                                └──Type expr: Variable: 20083
                                                                └──Type expr: Variable: 20008
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: 20083
                                                                   └──Type expr: Variable: 20008
                                                                └──Type expr: Variable: 20008
                                                          └──Desc: Variable
                                                             └──Variable: extract
                                                             └──Type expr: Variable: 20008
                                                             └──Type expr: Variable: 20083
                                                       └──Expression:
                                                          └──Type expr: Constructor: path
                                                             └──Type expr: Variable: 20083
                                                             └──Type expr: Variable: 20008
                                                          └──Desc: Variable
                                                             └──Variable: p
                                                 └──Expression:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: 20083
                                                       └──Type expr: Variable: 20008
                                                    └──Desc: Variable
                                                       └──Variable: l
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: path
                                                    └──Type expr: Variable: 20007
                                                    └──Type expr: Variable: 20008
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: 20007
                                                    └──Type expr: Variable: 20008
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: path
                                                       └──Type expr: Variable: 20007
                                                       └──Type expr: Variable: 20008
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Path_right
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: path
                                                                └──Type expr: Variable: 20139
                                                                └──Type expr: Variable: 20008
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: path
                                                                └──Type expr: Variable: 20007
                                                                └──Type expr: Variable: 20008
                                                       └──Pattern:
                                                          └──Type expr: Constructor: path
                                                             └──Type expr: Variable: 20139
                                                             └──Type expr: Variable: 20008
                                                          └──Desc: Variable: p
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: 20007
                                                       └──Type expr: Variable: 20008
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Tree_fork
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: 20136
                                                                   └──Type expr: Variable: 20008
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: 20134
                                                                   └──Type expr: Variable: 20008
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: 20007
                                                                └──Type expr: Variable: 20008
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: 20136
                                                                └──Type expr: Variable: 20008
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: 20134
                                                                └──Type expr: Variable: 20008
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: 20136
                                                                   └──Type expr: Variable: 20008
                                                                └──Desc: Any
                                                             └──Pattern:
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: 20134
                                                                   └──Type expr: Variable: 20008
                                                                └──Desc: Variable: r
                                           └──Expression:
                                              └──Type expr: Variable: 20008
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: 20134
                                                          └──Type expr: Variable: 20008
                                                       └──Type expr: Variable: 20008
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: path
                                                                └──Type expr: Variable: 20134
                                                                └──Type expr: Variable: 20008
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: 20134
                                                                   └──Type expr: Variable: 20008
                                                                └──Type expr: Variable: 20008
                                                          └──Desc: Variable
                                                             └──Variable: extract
                                                             └──Type expr: Variable: 20008
                                                             └──Type expr: Variable: 20134
                                                       └──Expression:
                                                          └──Type expr: Constructor: path
                                                             └──Type expr: Variable: 20134
                                                             └──Type expr: Variable: 20008
                                                          └──Desc: Variable
                                                             └──Variable: p
                                                 └──Expression:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: 20134
                                                       └──Type expr: Variable: 20008
                                                    └──Desc: Variable
                                                       └──Variable: r
       └──Structure item: Type
          └──Type declaration:
             └──Type name: le
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Le_zero
                   └──Constructor alphas: 19049 19050
                   └──Constructor type:
                      └──Type expr: Constructor: le
                         └──Type expr: Variable: 19049
                         └──Type expr: Variable: 19050
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: nat
                         └──Type expr: Variable: 19050
                   └──Constraint:
                      └──Type expr: Variable: 19049
                      └──Type expr: Constructor: zero
                └──Constructor declaration:
                   └──Constructor name: Le_succ
                   └──Constructor alphas: 19049 19050
                   └──Constructor type:
                      └──Type expr: Constructor: le
                         └──Type expr: Variable: 19049
                         └──Type expr: Variable: 19050
                   └──Constructor argument:
                      └──Constructor betas: 19055 19054
                      └──Type expr: Constructor: le
                         └──Type expr: Variable: 19054
                         └──Type expr: Variable: 19055
                   └──Constraint:
                      └──Type expr: Variable: 19049
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: 19054
                   └──Constraint:
                      └──Type expr: Variable: 19050
                      └──Type expr: Constructor: succ
                         └──Type expr: Variable: 19055
       └──Structure item: Type
          └──Type declaration:
             └──Type name: even
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Even_zero
                   └──Constructor alphas: 19060
                   └──Constructor type:
                      └──Type expr: Constructor: even
                         └──Type expr: Variable: 19060
                   └──Constraint:
                      └──Type expr: Variable: 19060
                      └──Type expr: Constructor: zero
                └──Constructor declaration:
                   └──Constructor name: Even_ssucc
                   └──Constructor alphas: 19060
                   └──Constructor type:
                      └──Type expr: Constructor: even
                         └──Type expr: Variable: 19060
                   └──Constructor argument:
                      └──Constructor betas: 19063
                      └──Type expr: Constructor: even
                         └──Type expr: Variable: 19063
                   └──Constraint:
                      └──Type expr: Variable: 19060
                      └──Type expr: Constructor: succ
                         └──Type expr: Constructor: succ
                            └──Type expr: Variable: 19063
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
                   └──Variables: 20331,20330,20329
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: plus
                            └──Type expr: Variable: 20357
                            └──Type expr: Variable: 20358
                            └──Type expr: Variable: 20359
                         └──Type expr: Constructor: le
                            └──Type expr: Variable: 20357
                            └──Type expr: Variable: 20359
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: plus
                               └──Type expr: Variable: 20357
                               └──Type expr: Variable: 20358
                               └──Type expr: Variable: 20359
                            └──Desc: Variable: p
                         └──Expression:
                            └──Type expr: Constructor: le
                               └──Type expr: Variable: 20357
                               └──Type expr: Variable: 20359
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: plus
                                     └──Type expr: Variable: 20357
                                     └──Type expr: Variable: 20358
                                     └──Type expr: Variable: 20359
                                  └──Desc: Variable
                                     └──Variable: p
                               └──Type expr: Constructor: plus
                                  └──Type expr: Variable: 20357
                                  └──Type expr: Variable: 20358
                                  └──Type expr: Variable: 20359
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: plus
                                           └──Type expr: Variable: 20357
                                           └──Type expr: Variable: 20358
                                           └──Type expr: Variable: 20359
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Plus_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: plus
                                                    └──Type expr: Variable: 20379
                                                    └──Type expr: Variable: 20358
                                                    └──Type expr: Variable: 20380
                                              └──Constructor type:
                                                 └──Type expr: Constructor: plus
                                                    └──Type expr: Variable: 20357
                                                    └──Type expr: Variable: 20358
                                                    └──Type expr: Variable: 20359
                                           └──Pattern:
                                              └──Type expr: Constructor: plus
                                                 └──Type expr: Variable: 20379
                                                 └──Type expr: Variable: 20358
                                                 └──Type expr: Variable: 20380
                                              └──Desc: Variable: p
                                     └──Expression:
                                        └──Type expr: Constructor: le
                                           └──Type expr: Variable: 20357
                                           └──Type expr: Variable: 20359
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Le_succ
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: le
                                                    └──Type expr: Variable: 20379
                                                    └──Type expr: Variable: 20380
                                              └──Constructor type:
                                                 └──Type expr: Constructor: le
                                                    └──Type expr: Variable: 20357
                                                    └──Type expr: Variable: 20359
                                           └──Expression:
                                              └──Type expr: Constructor: le
                                                 └──Type expr: Variable: 20379
                                                 └──Type expr: Variable: 20380
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: plus
                                                          └──Type expr: Variable: 20379
                                                          └──Type expr: Variable: 20358
                                                          └──Type expr: Variable: 20380
                                                       └──Type expr: Constructor: le
                                                          └──Type expr: Variable: 20379
                                                          └──Type expr: Variable: 20380
                                                    └──Desc: Variable
                                                       └──Variable: summand_less_than_sum
                                                       └──Type expr: Variable: 20380
                                                       └──Type expr: Variable: 20358
                                                       └──Type expr: Variable: 20379
                                                 └──Expression:
                                                    └──Type expr: Constructor: plus
                                                       └──Type expr: Variable: 20379
                                                       └──Type expr: Variable: 20358
                                                       └──Type expr: Variable: 20380
                                                    └──Desc: Variable
                                                       └──Variable: p
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: plus
                                           └──Type expr: Variable: 20357
                                           └──Type expr: Variable: 20358
                                           └──Type expr: Variable: 20359
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Plus_zero
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: nat
                                                    └──Type expr: Variable: 20358
                                              └──Constructor type:
                                                 └──Type expr: Constructor: plus
                                                    └──Type expr: Variable: 20357
                                                    └──Type expr: Variable: 20358
                                                    └──Type expr: Variable: 20359
                                           └──Pattern:
                                              └──Type expr: Constructor: nat
                                                 └──Type expr: Variable: 20358
                                              └──Desc: Variable: n
                                     └──Expression:
                                        └──Type expr: Constructor: le
                                           └──Type expr: Variable: 20357
                                           └──Type expr: Variable: 20359
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Le_zero
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: nat
                                                    └──Type expr: Variable: 20358
                                              └──Constructor type:
                                                 └──Type expr: Constructor: le
                                                    └──Type expr: Constructor: zero
                                                    └──Type expr: Variable: 20358
                                           └──Expression:
                                              └──Type expr: Constructor: nat
                                                 └──Type expr: Variable: 20358
                                              └──Desc: Variable
                                                 └──Variable: n |}]

