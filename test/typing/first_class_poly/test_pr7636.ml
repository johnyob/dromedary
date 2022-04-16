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
                   └──Alias alphas: 7407 7408
                   └──Type expr: Variable: 7407
       └──Structure item: Type
          └──Type declaration:
             └──Type name: iter
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: f
                   └──Label alphas: 7409
                   └──Label betas: 7410
                   └──Type expr: Arrow
                      └──Type expr: Constructor: elt
                         └──Type expr: Variable: 7409
                         └──Type expr: Variable: 7410
                      └──Type expr: Constructor: unit
                   └──Type expr: Constructor: iter
                      └──Type expr: Variable: 7409
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Constructor: elt
                            └──Type expr: Variable: 7439
                            └──Type expr: Variable: 7446
                         └──Type expr: Constructor: unit
                      └──Type expr: Constructor: iter
                         └──Type expr: Variable: 7439
                   └──Desc: Variable: promote
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Constructor: elt
                               └──Type expr: Variable: 7439
                               └──Type expr: Variable: 7446
                            └──Type expr: Constructor: unit
                         └──Type expr: Constructor: iter
                            └──Type expr: Variable: 7439
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: elt
                                  └──Type expr: Variable: 7439
                                  └──Type expr: Variable: 7446
                               └──Type expr: Constructor: unit
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Constructor: iter
                               └──Type expr: Variable: 7439
                            └──Desc: Let
                               └──Value bindings:
                                  └──Value binding:
                                     └──Pattern:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: elt
                                              └──Type expr: Variable: 7439
                                              └──Type expr: Variable: 7446
                                           └──Type expr: Constructor: unit
                                        └──Desc: Variable: g
                                     └──Abstraction:
                                        └──Variables:
                                        └──Expression:
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: elt
                                                 └──Type expr: Variable: 7439
                                                 └──Type expr: Variable: 7446
                                              └──Type expr: Constructor: unit
                                           └──Desc: Function
                                              └──Pattern:
                                                 └──Type expr: Constructor: elt
                                                    └──Type expr: Variable: 7439
                                                    └──Type expr: Variable: 7446
                                                 └──Desc: Variable: x
                                              └──Expression:
                                                 └──Type expr: Constructor: unit
                                                 └──Desc: Application
                                                    └──Expression:
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: elt
                                                             └──Type expr: Variable: 7439
                                                             └──Type expr: Variable: 7446
                                                          └──Type expr: Constructor: unit
                                                       └──Desc: Variable
                                                          └──Variable: f
                                                    └──Expression:
                                                       └──Type expr: Constructor: elt
                                                          └──Type expr: Variable: 7439
                                                          └──Type expr: Variable: 7446
                                                       └──Desc: Variable
                                                          └──Variable: x
                               └──Expression:
                                  └──Type expr: Constructor: iter
                                     └──Type expr: Variable: 7439
                                  └──Desc: Record
                                     └──Label description:
                                        └──Label: f
                                        └──Label argument type:
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: elt
                                                 └──Type expr: Variable: 7439
                                                 └──Type expr: Variable: 7446
                                              └──Type expr: Constructor: unit
                                        └──Label type:
                                           └──Type expr: Constructor: iter
                                              └──Type expr: Variable: 7439
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: elt
                                              └──Type expr: Variable: 7439
                                              └──Type expr: Variable: 7446
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
                   └──Alias alphas: 7452
                   └──Type expr: Constructor: int
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: int
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 7465
                   └──Desc: Variable: test
                └──Abstraction:
                   └──Variables: 7465
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: 7465
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: i
                         └──Expression:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: 7465
                            └──Desc: Variable
                               └──Variable: i |}]