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
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas: b
                      └──Type expr: Tuple
                         └──Type expr: Arrow
                            └──Type expr: Variable: a
                            └──Type expr: Variable: b
                         └──Type expr: Arrow
                            └──Type expr: Variable: b
                            └──Type expr: Variable: a
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: t
                      └──Type expr: Variable: a5069
                   └──Desc: Variable: t
                └──Abstraction:
                   └──Variables: a5069,a5069,a5069,a5069,a5069,a5069
                   └──Expression:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a5069
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Packed
                            └──Constructor argument type:
                               └──Type expr: Tuple
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a5069
                                     └──Type expr: Variable: a5069
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a5069
                                     └──Type expr: Variable: a5069
                            └──Constructor type:
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: a5069
                         └──Expression:
                            └──Type expr: Tuple
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a5069
                                  └──Type expr: Variable: a5069
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a5069
                                  └──Type expr: Variable: a5069
                            └──Desc: Tuple
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a5069
                                     └──Type expr: Variable: a5069
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: a5069
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: a5069
                                        └──Desc: Variable
                                           └──Variable: x
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a5069
                                     └──Type expr: Variable: a5069
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: a5069
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: a5069
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
                                                 └──Type expr: Variable: a5104
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: a5104
                                                 └──Type expr: Constructor: int
                                        └──Constructor type:
                                           └──Type expr: Constructor: t
                                              └──Type expr: Constructor: int
                                     └──Pattern:
                                        └──Type expr: Tuple
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: int
                                              └──Type expr: Variable: a5104
                                           └──Type expr: Arrow
                                              └──Type expr: Variable: a5104
                                              └──Type expr: Constructor: int
                                        └──Desc: Tuple
                                           └──Pattern:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Variable: a5104
                                              └──Desc: Variable: g
                                           └──Pattern:
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: a5104
                                                 └──Type expr: Constructor: int
                                              └──Desc: Variable: h
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: a5104
                                           └──Type expr: Constructor: int
                                        └──Desc: Variable
                                           └──Variable: h
                                     └──Expression:
                                        └──Type expr: Variable: a5104
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Variable: a5104
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
                      └──Type expr: Variable: a5150
                      └──Type expr: Variable: a5150
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: a5150,a5150,a5150,a5150,a5150
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a5150
                         └──Type expr: Variable: a5150
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a5150
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: a5150
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: a5150
                                  └──Desc: Variable
                                     └──Variable: t
                                     └──Type expr: Variable: a5150
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: a5150
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: a5150
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Packed
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: a5150
                                                       └──Type expr: Variable: a5140
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: a5140
                                                       └──Type expr: Variable: a5150
                                              └──Constructor type:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: a5150
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Arrow
                                                    └──Type expr: Variable: a5150
                                                    └──Type expr: Variable: a5140
                                                 └──Type expr: Arrow
                                                    └──Type expr: Variable: a5140
                                                    └──Type expr: Variable: a5150
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: a5150
                                                       └──Type expr: Variable: a5140
                                                    └──Desc: Variable: g
                                                 └──Pattern:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: a5140
                                                       └──Type expr: Variable: a5150
                                                    └──Desc: Variable: h
                                     └──Expression:
                                        └──Type expr: Variable: a5150
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: a5140
                                                 └──Type expr: Variable: a5150
                                              └──Desc: Variable
                                                 └──Variable: h
                                           └──Expression:
                                              └──Type expr: Variable: a5140
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: a5150
                                                       └──Type expr: Variable: a5140
                                                    └──Desc: Variable
                                                       └──Variable: g
                                                 └──Expression:
                                                    └──Type expr: Variable: a5150
                                                    └──Desc: Variable
                                                       └──Variable: x
       └──Structure item: Type
          └──Type declaration:
             └──Type name: iso
             └──Type declaration kind: Alias
                └──Alias
                   └──Alias name: iso
                   └──Alias alphas: a b
                   └──Type expr: Tuple
                      └──Type expr: Arrow
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                      └──Type expr: Arrow
                         └──Type expr: Variable: b
                         └──Type expr: Variable: a
       └──Structure item: Type
          └──Type declaration:
             └──Type name: ex_iso
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Iso
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: ex_iso
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas: b
                      └──Type expr: Constructor: iso
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: ex_iso
                      └──Type expr: Variable: a5161
                   └──Desc: Variable: t
                └──Abstraction:
                   └──Variables: a5161
                   └──Expression:
                      └──Type expr: Constructor: ex_iso
                         └──Type expr: Variable: a5161
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Iso
                            └──Constructor argument type:
                               └──Type expr: Tuple
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a5161
                                     └──Type expr: Variable: a5161
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a5161
                                     └──Type expr: Variable: a5161
                            └──Constructor type:
                               └──Type expr: Constructor: ex_iso
                                  └──Type expr: Variable: a5161
                         └──Expression:
                            └──Type expr: Tuple
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a5161
                                  └──Type expr: Variable: a5161
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a5161
                                  └──Type expr: Variable: a5161
                            └──Desc: Tuple
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a5161
                                     └──Type expr: Variable: a5161
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: a5161
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: a5161
                                        └──Desc: Variable
                                           └──Variable: x
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a5161
                                     └──Type expr: Variable: a5161
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: a5161
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: a5161
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
    ("Cannot unify types" (type_expr1 ((desc (Ttyp_var a142))))
     (type_expr2 ((desc (Ttyp_var a141))))) |}]