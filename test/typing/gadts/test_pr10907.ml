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
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: t
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Packed
                   └──Constructor alphas: 94
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 94
                   └──Constructor argument:
                      └──Constructor betas: 95
                      └──Type expr: Tuple
                         └──Type expr: Arrow
                            └──Type expr: Variable: 94
                            └──Type expr: Variable: 95
                         └──Type expr: Arrow
                            └──Type expr: Variable: 95
                            └──Type expr: Variable: 94
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: t
                      └──Type expr: Variable: 2
                   └──Desc: Variable: t
                └──Abstraction:
                   └──Variables: 2,2,2,2,2,2
                   └──Expression:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 2
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Packed
                            └──Constructor argument type:
                               └──Type expr: Tuple
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 2
                                     └──Type expr: Variable: 2
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 2
                                     └──Type expr: Variable: 2
                            └──Constructor type:
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: 2
                         └──Expression:
                            └──Type expr: Tuple
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 2
                                  └──Type expr: Variable: 2
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 2
                                  └──Type expr: Variable: 2
                            └──Desc: Tuple
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 2
                                     └──Type expr: Variable: 2
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: 2
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: 2
                                        └──Desc: Variable
                                           └──Variable: x
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 2
                                     └──Type expr: Variable: 2
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: 2
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: 2
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
                                                 └──Type expr: Variable: 37
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: 37
                                                 └──Type expr: Constructor: int
                                        └──Constructor type:
                                           └──Type expr: Constructor: t
                                              └──Type expr: Constructor: int
                                     └──Pattern:
                                        └──Type expr: Tuple
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: int
                                              └──Type expr: Variable: 37
                                           └──Type expr: Arrow
                                              └──Type expr: Variable: 37
                                              └──Type expr: Constructor: int
                                        └──Desc: Tuple
                                           └──Pattern:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Variable: 37
                                              └──Desc: Variable: g
                                           └──Pattern:
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: 37
                                                 └──Type expr: Constructor: int
                                              └──Desc: Variable: h
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: 37
                                           └──Type expr: Constructor: int
                                        └──Desc: Variable
                                           └──Variable: h
                                     └──Expression:
                                        └──Type expr: Variable: 37
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Variable: 37
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
                      └──Type expr: Variable: 83
                      └──Type expr: Variable: 83
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: 83,83,83,83,83
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 83
                         └──Type expr: Variable: 83
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 83
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: 83
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: 83
                                  └──Desc: Variable
                                     └──Variable: t
                                     └──Type expr: Variable: 83
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: 83
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: 83
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Packed
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 83
                                                       └──Type expr: Variable: 73
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 73
                                                       └──Type expr: Variable: 83
                                              └──Constructor type:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: 83
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Arrow
                                                    └──Type expr: Variable: 83
                                                    └──Type expr: Variable: 73
                                                 └──Type expr: Arrow
                                                    └──Type expr: Variable: 73
                                                    └──Type expr: Variable: 83
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 83
                                                       └──Type expr: Variable: 73
                                                    └──Desc: Variable: g
                                                 └──Pattern:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 73
                                                       └──Type expr: Variable: 83
                                                    └──Desc: Variable: h
                                     └──Expression:
                                        └──Type expr: Variable: 83
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: 73
                                                 └──Type expr: Variable: 83
                                              └──Desc: Variable
                                                 └──Variable: h
                                           └──Expression:
                                              └──Type expr: Variable: 73
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 83
                                                       └──Type expr: Variable: 73
                                                    └──Desc: Variable
                                                       └──Variable: g
                                                 └──Expression:
                                                    └──Type expr: Variable: 83
                                                    └──Desc: Variable
                                                       └──Variable: x
       └──Structure item: Type
          └──Type declaration:
             └──Type name: iso
             └──Type declaration kind: Alias
                └──Alias
                   └──Alias name: iso
                   └──Alias alphas: 100 101
                   └──Type expr: Tuple
                      └──Type expr: Arrow
                         └──Type expr: Variable: 100
                         └──Type expr: Variable: 101
                      └──Type expr: Arrow
                         └──Type expr: Variable: 101
                         └──Type expr: Variable: 100
       └──Structure item: Type
          └──Type declaration:
             └──Type name: ex_iso
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Iso
                   └──Constructor alphas: 105
                   └──Constructor type:
                      └──Type expr: Constructor: ex_iso
                         └──Type expr: Variable: 105
                   └──Constructor argument:
                      └──Constructor betas: 106
                      └──Type expr: Constructor: iso
                         └──Type expr: Variable: 105
                         └──Type expr: Variable: 106
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: ex_iso
                      └──Type expr: Variable: 94
                   └──Desc: Variable: t
                └──Abstraction:
                   └──Variables: 94
                   └──Expression:
                      └──Type expr: Constructor: ex_iso
                         └──Type expr: Variable: 94
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Iso
                            └──Constructor argument type:
                               └──Type expr: Tuple
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 94
                                     └──Type expr: Variable: 94
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 94
                                     └──Type expr: Variable: 94
                            └──Constructor type:
                               └──Type expr: Constructor: ex_iso
                                  └──Type expr: Variable: 94
                         └──Expression:
                            └──Type expr: Tuple
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 94
                                  └──Type expr: Variable: 94
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 94
                                  └──Type expr: Variable: 94
                            └──Desc: Tuple
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 94
                                     └──Type expr: Variable: 94
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: 94
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: 94
                                        └──Desc: Variable
                                           └──Variable: x
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 94
                                     └──Type expr: Variable: 94
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: 94
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: 94
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
  [%expect
    {|
    ("Cannot unify types" ("Type_expr.decode type_expr1" (Type 67 (Var 67)))
     ("Type_expr.decode type_expr2" (Type 72 (Var 72)))) |}]
