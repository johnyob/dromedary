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
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: s
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: nil
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: s
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas: b c
                      └──Type expr: Constructor: s
                         └──Type expr: Variable: b
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Arrow
                         └──Type expr: Variable: c
                         └──Type expr: Variable: b
       └──Structure item: Type
          └──Type declaration:
             └──Type name: var
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Head
                   └──Constructor alphas: stack t
                   └──Constructor type:
                      └──Type expr: Constructor: var
                         └──Type expr: Variable: stack
                         └──Type expr: Variable: t
                   └──Constructor argument:
                      └──Constructor betas: s
                      └──Type expr: Constructor: unit
                   └──Constraint:
                      └──Type expr: Variable: stack
                      └──Type expr: Constructor: s
                         └──Type expr: Arrow
                            └──Type expr: Variable: t
                            └──Type expr: Variable: s
                └──Constructor declaration:
                   └──Constructor name: Tail
                   └──Constructor alphas: stack t
                   └──Constructor type:
                      └──Type expr: Constructor: var
                         └──Type expr: Variable: stack
                         └──Type expr: Variable: t
                   └──Constructor argument:
                      └──Constructor betas: tail a
                      └──Type expr: Constructor: var
                         └──Type expr: Constructor: s
                            └──Type expr: Variable: tail
                         └──Type expr: Variable: t
                   └──Constraint:
                      └──Type expr: Variable: stack
                      └──Type expr: Constructor: s
                         └──Type expr: Arrow
                            └──Type expr: Variable: a
                            └──Type expr: Variable: tail
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
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: nil
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas: h t
                      └──Type expr: Tuple
                         └──Type expr: Variable: h
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: t
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Arrow
                         └──Type expr: Variable: h
                         └──Type expr: Variable: t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: get_var
                └──Abstraction:
                   └──Variables: a5077,a5079
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: var
                            └──Type expr: Constructor: s
                               └──Type expr: Variable: a5111
                            └──Type expr: Variable: a5109
                         └──Type expr: Arrow
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a5111
                            └──Type expr: Variable: a5109
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: var
                               └──Type expr: Constructor: s
                                  └──Type expr: Variable: a5111
                               └──Type expr: Variable: a5109
                            └──Desc: Variable: n
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a5111
                               └──Type expr: Variable: a5109
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: a5111
                                  └──Desc: Variable: s
                               └──Expression:
                                  └──Type expr: Variable: a5109
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: var
                                              └──Type expr: Constructor: s
                                                 └──Type expr: Variable: a5111
                                              └──Type expr: Variable: a5109
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a5111
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: var
                                                 └──Type expr: Constructor: s
                                                    └──Type expr: Variable: a5111
                                                 └──Type expr: Variable: a5109
                                              └──Desc: Variable
                                                 └──Variable: n
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a5111
                                              └──Desc: Variable
                                                 └──Variable: s
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: var
                                           └──Type expr: Constructor: s
                                              └──Type expr: Variable: a5111
                                           └──Type expr: Variable: a5109
                                        └──Type expr: Constructor: list
                                           └──Type expr: Variable: a5111
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: var
                                                    └──Type expr: Constructor: s
                                                       └──Type expr: Variable: a5111
                                                    └──Type expr: Variable: a5109
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: a5111
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: var
                                                       └──Type expr: Constructor: s
                                                          └──Type expr: Variable: a5111
                                                       └──Type expr: Variable: a5109
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Head
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Constructor: s
                                                                   └──Type expr: Variable: a5111
                                                                └──Type expr: Variable: a5109
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a5111
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Cons
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a5147
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a5149
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a5111
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a5147
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a5149
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Variable: a5147
                                                                └──Desc: Variable: h
                                                             └──Pattern:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a5149
                                                                └──Desc: Any
                                           └──Expression:
                                              └──Type expr: Variable: a5109
                                              └──Desc: Variable
                                                 └──Variable: h
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: var
                                                    └──Type expr: Constructor: s
                                                       └──Type expr: Variable: a5111
                                                    └──Type expr: Variable: a5109
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: a5111
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: var
                                                       └──Type expr: Constructor: s
                                                          └──Type expr: Variable: a5111
                                                       └──Type expr: Variable: a5109
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Tail
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Constructor: s
                                                                   └──Type expr: Variable: a5189
                                                                └──Type expr: Variable: a5109
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Constructor: s
                                                                   └──Type expr: Variable: a5111
                                                                └──Type expr: Variable: a5109
                                                       └──Pattern:
                                                          └──Type expr: Constructor: var
                                                             └──Type expr: Constructor: s
                                                                └──Type expr: Variable: a5189
                                                             └──Type expr: Variable: a5109
                                                          └──Desc: Variable: n'
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a5111
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Cons
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a5183
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a5185
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a5111
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a5183
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a5185
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Variable: a5183
                                                                └──Desc: Any
                                                             └──Pattern:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a5185
                                                                └──Desc: Variable: t
                                           └──Expression:
                                              └──Type expr: Variable: a5109
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a5185
                                                       └──Type expr: Variable: a5109
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Constructor: s
                                                                   └──Type expr: Variable: a5185
                                                                └──Type expr: Variable: a5109
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a5185
                                                                └──Type expr: Variable: a5109
                                                          └──Desc: Variable
                                                             └──Variable: get_var
                                                             └──Type expr: Variable: a5109
                                                             └──Type expr: Variable: a5185
                                                       └──Expression:
                                                          └──Type expr: Constructor: var
                                                             └──Type expr: Constructor: s
                                                                └──Type expr: Variable: a5185
                                                             └──Type expr: Variable: a5109
                                                          └──Desc: Variable
                                                             └──Variable: n'
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a5185
                                                    └──Desc: Variable
                                                       └──Variable: t |}]