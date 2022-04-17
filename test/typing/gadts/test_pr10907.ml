open! Import
open Util

let%expect_test "" = 
  let str = 
    {|
      type 'a t = 
        | Packed of 'b. ('a -> 'b) * ('b -> 'a)
      ;;

      let t = 
        Packed ((fun x -> x), (fun x -> x))
      ;;

      let t1 = 
        match t with
        ( Packed (g, h) -> h (g 1) )
      ;;

      let f = 
        fun x ->
          match t with
          ( Packed (g, h) -> h (g x))
      ;;

      type ('a, 'b) iso = ('a -> 'b) * ('b -> 'a);;

      type 'a ex_iso = 
        | Iso of 'b. ('a, 'b) iso
      ;;

      let (type 'a) t = 
        (Iso ((fun x -> x), (fun x -> x)) : 'a ex_iso)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: t
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Packed
                   └──Constructor alphas: 17012
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 17012
                   └──Constructor argument:
                      └──Constructor betas: 17013
                      └──Type expr: Tuple
                         └──Type expr: Arrow
                            └──Type expr: Variable: 17012
                            └──Type expr: Variable: 17013
                         └──Type expr: Arrow
                            └──Type expr: Variable: 17013
                            └──Type expr: Variable: 17012
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: t
                      └──Type expr: Variable: 17029
                   └──Desc: Variable: t
                └──Abstraction:
                   └──Variables: 17029,17029,17029,17029,17029,17029
                   └──Expression:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 17029
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Packed
                            └──Constructor argument type:
                               └──Type expr: Tuple
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 17029
                                     └──Type expr: Variable: 17029
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 17029
                                     └──Type expr: Variable: 17029
                            └──Constructor type:
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: 17029
                         └──Expression:
                            └──Type expr: Tuple
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 17029
                                  └──Type expr: Variable: 17029
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 17029
                                  └──Type expr: Variable: 17029
                            └──Desc: Tuple
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 17029
                                     └──Type expr: Variable: 17029
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: 17029
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: 17029
                                        └──Desc: Variable
                                           └──Variable: x
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 17029
                                     └──Type expr: Variable: 17029
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: 17029
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: 17029
                                        └──Desc: Variable
                                           └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: int
                   └──Desc: Variable: t1
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: int
                      └──Desc: Match
                         └──Expression:
                            └──Type expr: Constructor: t
                               └──Type expr: Constructor: int
                            └──Desc: Variable
                               └──Variable: t
                               └──Type expr: Constructor: int
                         └──Type expr: Constructor: t
                            └──Type expr: Constructor: int
                         └──Cases:
                            └──Case:
                               └──Pattern:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Constructor: int
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Packed
                                        └──Constructor argument type:
                                           └──Type expr: Tuple
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Variable: 17064
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: 17064
                                                 └──Type expr: Constructor: int
                                        └──Constructor type:
                                           └──Type expr: Constructor: t
                                              └──Type expr: Constructor: int
                                     └──Pattern:
                                        └──Type expr: Tuple
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: int
                                              └──Type expr: Variable: 17064
                                           └──Type expr: Arrow
                                              └──Type expr: Variable: 17064
                                              └──Type expr: Constructor: int
                                        └──Desc: Tuple
                                           └──Pattern:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Variable: 17064
                                              └──Desc: Variable: g
                                           └──Pattern:
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: 17064
                                                 └──Type expr: Constructor: int
                                              └──Desc: Variable: h
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: 17064
                                           └──Type expr: Constructor: int
                                        └──Desc: Variable
                                           └──Variable: h
                                     └──Expression:
                                        └──Type expr: Variable: 17064
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Variable: 17064
                                              └──Desc: Variable
                                                 └──Variable: g
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 1
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 17110
                      └──Type expr: Variable: 17110
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: 17110,17110,17110,17110,17110
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 17110
                         └──Type expr: Variable: 17110
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 17110
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: 17110
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: 17110
                                  └──Desc: Variable
                                     └──Variable: t
                                     └──Type expr: Variable: 17110
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: 17110
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: 17110
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Packed
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 17110
                                                       └──Type expr: Variable: 17100
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 17100
                                                       └──Type expr: Variable: 17110
                                              └──Constructor type:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: 17110
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Arrow
                                                    └──Type expr: Variable: 17110
                                                    └──Type expr: Variable: 17100
                                                 └──Type expr: Arrow
                                                    └──Type expr: Variable: 17100
                                                    └──Type expr: Variable: 17110
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 17110
                                                       └──Type expr: Variable: 17100
                                                    └──Desc: Variable: g
                                                 └──Pattern:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 17100
                                                       └──Type expr: Variable: 17110
                                                    └──Desc: Variable: h
                                     └──Expression:
                                        └──Type expr: Variable: 17110
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: 17100
                                                 └──Type expr: Variable: 17110
                                              └──Desc: Variable
                                                 └──Variable: h
                                           └──Expression:
                                              └──Type expr: Variable: 17100
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 17110
                                                       └──Type expr: Variable: 17100
                                                    └──Desc: Variable
                                                       └──Variable: g
                                                 └──Expression:
                                                    └──Type expr: Variable: 17110
                                                    └──Desc: Variable
                                                       └──Variable: x
       └──Structure item: Type
          └──Type declaration:
             └──Type name: iso
             └──Type declaration kind: Alias
                └──Alias
                   └──Alias name: iso
                   └──Alias alphas: 17018 17019
                   └──Type expr: Tuple
                      └──Type expr: Arrow
                         └──Type expr: Variable: 17018
                         └──Type expr: Variable: 17019
                      └──Type expr: Arrow
                         └──Type expr: Variable: 17019
                         └──Type expr: Variable: 17018
       └──Structure item: Type
          └──Type declaration:
             └──Type name: ex_iso
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Iso
                   └──Constructor alphas: 17023
                   └──Constructor type:
                      └──Type expr: Constructor: ex_iso
                         └──Type expr: Variable: 17023
                   └──Constructor argument:
                      └──Constructor betas: 17024
                      └──Type expr: Constructor: iso
                         └──Type expr: Variable: 17023
                         └──Type expr: Variable: 17024
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: ex_iso
                      └──Type expr: Variable: 17121
                   └──Desc: Variable: t
                └──Abstraction:
                   └──Variables: 17121
                   └──Expression:
                      └──Type expr: Constructor: ex_iso
                         └──Type expr: Variable: 17121
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Iso
                            └──Constructor argument type:
                               └──Type expr: Tuple
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 17121
                                     └──Type expr: Variable: 17121
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 17121
                                     └──Type expr: Variable: 17121
                            └──Constructor type:
                               └──Type expr: Constructor: ex_iso
                                  └──Type expr: Variable: 17121
                         └──Expression:
                            └──Type expr: Tuple
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 17121
                                  └──Type expr: Variable: 17121
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 17121
                                  └──Type expr: Variable: 17121
                            └──Desc: Tuple
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 17121
                                     └──Type expr: Variable: 17121
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: 17121
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: 17121
                                        └──Desc: Variable
                                           └──Variable: x
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 17121
                                     └──Type expr: Variable: 17121
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: 17121
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: 17121
                                        └──Desc: Variable
                                           └──Variable: x |}]

let%expect_test "" = 
  let str = 
    {|
      type ('a, 'b) iso = ('a -> 'b) * ('b -> 'a);;
      type 'a ex_iso = 
        | Iso of 'b. ('a, 'b) iso
      ;;

      let (type 'a) t = 
        (Iso ((fun x -> x), (fun x -> x)) : 'a ex_iso)
      ;;

      let (type 'a 'b) unsound_cast = 
        fun (x : 'a) ->
          (match t with ( Iso (g, h) -> h (g x) ) : 'b)
      ;; 
    |}
  in
  print_infer_result str;
  [%expect {|
    ("Cannot unify types"
     ("Type_expr.decode type_expr1" (Type 17224 (Var 17224)))
     ("Type_expr.decode type_expr2" (Type 17229 (Var 17229)))) |}]