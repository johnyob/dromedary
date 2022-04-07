open! Import
open Util

let%expect_test "pr7637-1" =
  let str = 
    {|
      type ('a, 'b) elt = 'a;;

      type 'a iter = { f : 'b. ('a, 'b) elt -> unit };;

      let promote = 
        exists (type 'a) ->
        fun (f : 'a -> unit) ->
          let g = fun x -> f x in
          { f = g }
      ;;  
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: elt
             └──Type declaration kind: Alias
                └──Alias
                   └──Alias name: elt
                   └──Alias alphas: a b
                   └──Type expr: Variable: a
       └──Structure item: Type
          └──Type declaration:
             └──Type name: iter
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: f
                   └──Label alphas: a
                   └──Label betas: b
                   └──Type expr: Arrow
                      └──Type expr: Constructor: elt
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                      └──Type expr: Constructor: unit
                   └──Type expr: Constructor: iter
                      └──Type expr: Variable: a
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Constructor: elt
                            └──Type expr: Variable: a4604
                            └──Type expr: Variable: a4611
                         └──Type expr: Constructor: unit
                      └──Type expr: Constructor: iter
                         └──Type expr: Variable: a4604
                   └──Desc: Variable: promote
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Constructor: elt
                               └──Type expr: Variable: a4604
                               └──Type expr: Variable: a4611
                            └──Type expr: Constructor: unit
                         └──Type expr: Constructor: iter
                            └──Type expr: Variable: a4604
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: elt
                                  └──Type expr: Variable: a4604
                                  └──Type expr: Variable: a4611
                               └──Type expr: Constructor: unit
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Constructor: iter
                               └──Type expr: Variable: a4604
                            └──Desc: Let
                               └──Value bindings:
                                  └──Value binding:
                                     └──Pattern:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: elt
                                              └──Type expr: Variable: a4604
                                              └──Type expr: Variable: a4611
                                           └──Type expr: Constructor: unit
                                        └──Desc: Variable: g
                                     └──Abstraction:
                                        └──Variables:
                                        └──Expression:
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: elt
                                                 └──Type expr: Variable: a4604
                                                 └──Type expr: Variable: a4611
                                              └──Type expr: Constructor: unit
                                           └──Desc: Function
                                              └──Pattern:
                                                 └──Type expr: Constructor: elt
                                                    └──Type expr: Variable: a4604
                                                    └──Type expr: Variable: a4611
                                                 └──Desc: Variable: x
                                              └──Expression:
                                                 └──Type expr: Constructor: unit
                                                 └──Desc: Application
                                                    └──Expression:
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: elt
                                                             └──Type expr: Variable: a4604
                                                             └──Type expr: Variable: a4611
                                                          └──Type expr: Constructor: unit
                                                       └──Desc: Variable
                                                          └──Variable: f
                                                    └──Expression:
                                                       └──Type expr: Constructor: elt
                                                          └──Type expr: Variable: a4604
                                                          └──Type expr: Variable: a4611
                                                       └──Desc: Variable
                                                          └──Variable: x
                               └──Expression:
                                  └──Type expr: Constructor: iter
                                     └──Type expr: Variable: a4604
                                  └──Desc: Record
                                     └──Label description:
                                        └──Label: f
                                        └──Label argument type:
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: elt
                                                 └──Type expr: Variable: a4604
                                                 └──Type expr: Variable: a4611
                                              └──Type expr: Constructor: unit
                                        └──Label type:
                                           └──Type expr: Constructor: iter
                                              └──Type expr: Variable: a4604
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: elt
                                              └──Type expr: Variable: a4604
                                              └──Type expr: Variable: a4611
                                           └──Type expr: Constructor: unit
                                        └──Desc: Variable
                                           └──Variable: g |}]

let%expect_test "pr7637-2" =
  let str = 
    {|
      type 'a t = int;;

      let (type 'a) test = 
        fun (i : int) -> (i : 'a t)
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
             └──Type declaration kind: Alias
                └──Alias
                   └──Alias name: t
                   └──Alias alphas: a
                   └──Type expr: Constructor: int
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: int
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a4628
                   └──Desc: Variable: test
                └──Abstraction:
                   └──Variables: a4628
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a4628
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: i
                         └──Expression:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: a4628
                            └──Desc: Variable
                               └──Variable: i |}]