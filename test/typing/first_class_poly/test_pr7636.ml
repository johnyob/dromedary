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
                   └──Alias alphas: 10 11
                   └──Type expr: Variable: 10
       └──Structure item: Type
          └──Type declaration:
             └──Type name: iter
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: f
                   └──Label alphas: 12
                   └──Label betas: 13
                   └──Type expr: Arrow
                      └──Type expr: Constructor: elt
                         └──Type expr: Variable: 12
                         └──Type expr: Variable: 13
                      └──Type expr: Constructor: unit
                   └──Type expr: Constructor: iter
                      └──Type expr: Variable: 12
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Constructor: elt
                            └──Type expr: Variable: 24
                            └──Type expr: Variable: 31
                         └──Type expr: Constructor: unit
                      └──Type expr: Constructor: iter
                         └──Type expr: Variable: 24
                   └──Desc: Variable: promote
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Constructor: elt
                               └──Type expr: Variable: 24
                               └──Type expr: Variable: 31
                            └──Type expr: Constructor: unit
                         └──Type expr: Constructor: iter
                            └──Type expr: Variable: 24
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: elt
                                  └──Type expr: Variable: 24
                                  └──Type expr: Variable: 31
                               └──Type expr: Constructor: unit
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Constructor: iter
                               └──Type expr: Variable: 24
                            └──Desc: Let
                               └──Value bindings:
                                  └──Value binding:
                                     └──Pattern:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: elt
                                              └──Type expr: Variable: 24
                                              └──Type expr: Variable: 31
                                           └──Type expr: Constructor: unit
                                        └──Desc: Variable: g
                                     └──Abstraction:
                                        └──Variables:
                                        └──Expression:
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: elt
                                                 └──Type expr: Variable: 24
                                                 └──Type expr: Variable: 31
                                              └──Type expr: Constructor: unit
                                           └──Desc: Function
                                              └──Pattern:
                                                 └──Type expr: Constructor: elt
                                                    └──Type expr: Variable: 24
                                                    └──Type expr: Variable: 31
                                                 └──Desc: Variable: x
                                              └──Expression:
                                                 └──Type expr: Constructor: unit
                                                 └──Desc: Application
                                                    └──Expression:
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: elt
                                                             └──Type expr: Variable: 24
                                                             └──Type expr: Variable: 31
                                                          └──Type expr: Constructor: unit
                                                       └──Desc: Variable
                                                          └──Variable: f
                                                    └──Expression:
                                                       └──Type expr: Constructor: elt
                                                          └──Type expr: Variable: 24
                                                          └──Type expr: Variable: 31
                                                       └──Desc: Variable
                                                          └──Variable: x
                               └──Expression:
                                  └──Type expr: Constructor: iter
                                     └──Type expr: Variable: 24
                                  └──Desc: Record
                                     └──Label description:
                                        └──Label: f
                                        └──Label argument type:
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: elt
                                                 └──Type expr: Variable: 24
                                                 └──Type expr: Variable: 31
                                              └──Type expr: Constructor: unit
                                        └──Label type:
                                           └──Type expr: Constructor: iter
                                              └──Type expr: Variable: 24
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: elt
                                              └──Type expr: Variable: 24
                                              └──Type expr: Variable: 31
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
                   └──Alias alphas: 37
                   └──Type expr: Constructor: int
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: int
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 11
                   └──Desc: Variable: test
                └──Abstraction:
                   └──Variables: 11
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: 11
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: i
                         └──Expression:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: 11
                            └──Desc: Variable
                               └──Variable: i |}]