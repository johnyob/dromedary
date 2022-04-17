open! Import
open Util

let%expect_test "" = 
  let str = 
    {|
      type nil = Cstr;;

      type 'a s = 
        | Nil constraint 'a = nil
        | Cons of 'b 'c. 'b s constraint 'a = 'c -> 'b
      ;;

      type ('stack, 't) var = 
        | Head of 's. unit constraint 'stack = ('t -> 's) s
        | Tail of 'tail 'a. ('tail s, 't) var constraint 'stack = ('a -> 'tail) s
      ;;

      type 'a list = 
        | Nil constraint 'a = nil
        | Cons of 'h 't. 'h * 't list constraint 'a = 'h -> 't
      ;;

      let rec (type 'stk 'ret) get_var = 
        fun (n : ('stk s, 'ret) var) (s : 'stk list) ->
          (match (n, s) with
           ( (Head (), Cons (h, _)) -> h
           | (Tail n', Cons (_, t)) -> get_var n' t
           )
          : 'ret)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: nil
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Cstr
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: nil
       └──Structure item: Type
          └──Type declaration:
             └──Type name: s
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: 15819
                   └──Constructor type:
                      └──Type expr: Constructor: s
                         └──Type expr: Variable: 15819
                   └──Constraint:
                      └──Type expr: Variable: 15819
                      └──Type expr: Constructor: nil
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 15819
                   └──Constructor type:
                      └──Type expr: Constructor: s
                         └──Type expr: Variable: 15819
                   └──Constructor argument:
                      └──Constructor betas: 15823 15822
                      └──Type expr: Constructor: s
                         └──Type expr: Variable: 15822
                   └──Constraint:
                      └──Type expr: Variable: 15819
                      └──Type expr: Arrow
                         └──Type expr: Variable: 15823
                         └──Type expr: Variable: 15822
       └──Structure item: Type
          └──Type declaration:
             └──Type name: var
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Head
                   └──Constructor alphas: 15827 15828
                   └──Constructor type:
                      └──Type expr: Constructor: var
                         └──Type expr: Variable: 15827
                         └──Type expr: Variable: 15828
                   └──Constructor argument:
                      └──Constructor betas: 15829
                      └──Type expr: Constructor: unit
                   └──Constraint:
                      └──Type expr: Variable: 15827
                      └──Type expr: Constructor: s
                         └──Type expr: Arrow
                            └──Type expr: Variable: 15828
                            └──Type expr: Variable: 15829
                └──Constructor declaration:
                   └──Constructor name: Tail
                   └──Constructor alphas: 15827 15828
                   └──Constructor type:
                      └──Type expr: Constructor: var
                         └──Type expr: Variable: 15827
                         └──Type expr: Variable: 15828
                   └──Constructor argument:
                      └──Constructor betas: 15835 15834
                      └──Type expr: Constructor: var
                         └──Type expr: Constructor: s
                            └──Type expr: Variable: 15834
                         └──Type expr: Variable: 15828
                   └──Constraint:
                      └──Type expr: Variable: 15827
                      └──Type expr: Constructor: s
                         └──Type expr: Arrow
                            └──Type expr: Variable: 15835
                            └──Type expr: Variable: 15834
       └──Structure item: Type
          └──Type declaration:
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: 15841
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 15841
                   └──Constraint:
                      └──Type expr: Variable: 15841
                      └──Type expr: Constructor: nil
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 15841
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 15841
                   └──Constructor argument:
                      └──Constructor betas: 15845 15844
                      └──Type expr: Tuple
                         └──Type expr: Variable: 15844
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 15845
                   └──Constraint:
                      └──Type expr: Variable: 15841
                      └──Type expr: Arrow
                         └──Type expr: Variable: 15844
                         └──Type expr: Variable: 15845
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: get_var
                └──Abstraction:
                   └──Variables: 15860,15862
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: var
                            └──Type expr: Constructor: s
                               └──Type expr: Variable: 15894
                            └──Type expr: Variable: 15892
                         └──Type expr: Arrow
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: 15894
                            └──Type expr: Variable: 15892
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: var
                               └──Type expr: Constructor: s
                                  └──Type expr: Variable: 15894
                               └──Type expr: Variable: 15892
                            └──Desc: Variable: n
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: 15894
                               └──Type expr: Variable: 15892
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: 15894
                                  └──Desc: Variable: s
                               └──Expression:
                                  └──Type expr: Variable: 15892
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: var
                                              └──Type expr: Constructor: s
                                                 └──Type expr: Variable: 15894
                                              └──Type expr: Variable: 15892
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: 15894
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: var
                                                 └──Type expr: Constructor: s
                                                    └──Type expr: Variable: 15894
                                                 └──Type expr: Variable: 15892
                                              └──Desc: Variable
                                                 └──Variable: n
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: 15894
                                              └──Desc: Variable
                                                 └──Variable: s
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: var
                                           └──Type expr: Constructor: s
                                              └──Type expr: Variable: 15894
                                           └──Type expr: Variable: 15892
                                        └──Type expr: Constructor: list
                                           └──Type expr: Variable: 15894
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: var
                                                    └──Type expr: Constructor: s
                                                       └──Type expr: Variable: 15894
                                                    └──Type expr: Variable: 15892
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: 15894
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: var
                                                       └──Type expr: Constructor: s
                                                          └──Type expr: Variable: 15894
                                                       └──Type expr: Variable: 15892
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Head
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Constructor: s
                                                                   └──Type expr: Variable: 15894
                                                                └──Type expr: Variable: 15892
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: 15894
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Cons
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 15930
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: 15932
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: 15894
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 15930
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: 15932
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Variable: 15930
                                                                └──Desc: Variable: h
                                                             └──Pattern:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: 15932
                                                                └──Desc: Any
                                           └──Expression:
                                              └──Type expr: Variable: 15892
                                              └──Desc: Variable
                                                 └──Variable: h
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: var
                                                    └──Type expr: Constructor: s
                                                       └──Type expr: Variable: 15894
                                                    └──Type expr: Variable: 15892
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: 15894
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: var
                                                       └──Type expr: Constructor: s
                                                          └──Type expr: Variable: 15894
                                                       └──Type expr: Variable: 15892
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Tail
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Constructor: s
                                                                   └──Type expr: Variable: 15972
                                                                └──Type expr: Variable: 15892
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Constructor: s
                                                                   └──Type expr: Variable: 15894
                                                                └──Type expr: Variable: 15892
                                                       └──Pattern:
                                                          └──Type expr: Constructor: var
                                                             └──Type expr: Constructor: s
                                                                └──Type expr: Variable: 15972
                                                             └──Type expr: Variable: 15892
                                                          └──Desc: Variable: n'
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: 15894
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Cons
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 15966
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: 15968
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: 15894
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 15966
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: 15968
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Variable: 15966
                                                                └──Desc: Any
                                                             └──Pattern:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: 15968
                                                                └──Desc: Variable: t
                                           └──Expression:
                                              └──Type expr: Variable: 15892
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: 15968
                                                       └──Type expr: Variable: 15892
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Constructor: s
                                                                   └──Type expr: Variable: 15968
                                                                └──Type expr: Variable: 15892
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: 15968
                                                                └──Type expr: Variable: 15892
                                                          └──Desc: Variable
                                                             └──Variable: get_var
                                                             └──Type expr: Variable: 15892
                                                             └──Type expr: Variable: 15968
                                                       └──Expression:
                                                          └──Type expr: Constructor: var
                                                             └──Type expr: Constructor: s
                                                                └──Type expr: Variable: 15968
                                                             └──Type expr: Variable: 15892
                                                          └──Desc: Variable
                                                             └──Variable: n'
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: 15968
                                                    └──Desc: Variable
                                                       └──Variable: t |}]