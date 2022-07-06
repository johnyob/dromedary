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
                   └──Constructor alphas: 86
                   └──Constructor type:
                      └──Type expr: Constructor: s
                         └──Type expr: Variable: 86
                   └──Constraint:
                      └──Type expr: Variable: 86
                      └──Type expr: Constructor: nil
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 86
                   └──Constructor type:
                      └──Type expr: Constructor: s
                         └──Type expr: Variable: 86
                   └──Constructor argument:
                      └──Constructor betas: 90 89
                      └──Type expr: Constructor: s
                         └──Type expr: Variable: 89
                   └──Constraint:
                      └──Type expr: Variable: 86
                      └──Type expr: Arrow
                         └──Type expr: Variable: 90
                         └──Type expr: Variable: 89
       └──Structure item: Type
          └──Type declaration:
             └──Type name: var
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Head
                   └──Constructor alphas: 94 95
                   └──Constructor type:
                      └──Type expr: Constructor: var
                         └──Type expr: Variable: 94
                         └──Type expr: Variable: 95
                   └──Constructor argument:
                      └──Constructor betas: 96
                      └──Type expr: Constructor: unit
                   └──Constraint:
                      └──Type expr: Variable: 94
                      └──Type expr: Constructor: s
                         └──Type expr: Arrow
                            └──Type expr: Variable: 95
                            └──Type expr: Variable: 96
                └──Constructor declaration:
                   └──Constructor name: Tail
                   └──Constructor alphas: 94 95
                   └──Constructor type:
                      └──Type expr: Constructor: var
                         └──Type expr: Variable: 94
                         └──Type expr: Variable: 95
                   └──Constructor argument:
                      └──Constructor betas: 102 101
                      └──Type expr: Constructor: var
                         └──Type expr: Constructor: s
                            └──Type expr: Variable: 101
                         └──Type expr: Variable: 95
                   └──Constraint:
                      └──Type expr: Variable: 94
                      └──Type expr: Constructor: s
                         └──Type expr: Arrow
                            └──Type expr: Variable: 102
                            └──Type expr: Variable: 101
       └──Structure item: Type
          └──Type declaration:
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: 108
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 108
                   └──Constraint:
                      └──Type expr: Variable: 108
                      └──Type expr: Constructor: nil
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 108
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: 108
                   └──Constructor argument:
                      └──Constructor betas: 112 111
                      └──Type expr: Tuple
                         └──Type expr: Variable: 111
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: 112
                   └──Constraint:
                      └──Type expr: Variable: 108
                      └──Type expr: Arrow
                         └──Type expr: Variable: 111
                         └──Type expr: Variable: 112
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: get_var
                └──Abstraction:
                   └──Variables: 10,12
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: var
                            └──Type expr: Constructor: s
                               └──Type expr: Variable: 44
                            └──Type expr: Variable: 42
                         └──Type expr: Arrow
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: 44
                            └──Type expr: Variable: 42
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: var
                               └──Type expr: Constructor: s
                                  └──Type expr: Variable: 44
                               └──Type expr: Variable: 42
                            └──Desc: Variable: n
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: 44
                               └──Type expr: Variable: 42
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: 44
                                  └──Desc: Variable: s
                               └──Expression:
                                  └──Type expr: Variable: 42
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: var
                                              └──Type expr: Constructor: s
                                                 └──Type expr: Variable: 44
                                              └──Type expr: Variable: 42
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: 44
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: var
                                                 └──Type expr: Constructor: s
                                                    └──Type expr: Variable: 44
                                                 └──Type expr: Variable: 42
                                              └──Desc: Variable
                                                 └──Variable: n
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: 44
                                              └──Desc: Variable
                                                 └──Variable: s
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: var
                                           └──Type expr: Constructor: s
                                              └──Type expr: Variable: 44
                                           └──Type expr: Variable: 42
                                        └──Type expr: Constructor: list
                                           └──Type expr: Variable: 44
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: var
                                                    └──Type expr: Constructor: s
                                                       └──Type expr: Variable: 44
                                                    └──Type expr: Variable: 42
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: 44
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: var
                                                       └──Type expr: Constructor: s
                                                          └──Type expr: Variable: 44
                                                       └──Type expr: Variable: 42
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Head
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Constructor: s
                                                                   └──Type expr: Variable: 44
                                                                └──Type expr: Variable: 42
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: 44
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Cons
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 80
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: 82
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: 44
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 80
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: 82
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Variable: 80
                                                                └──Desc: Variable: h
                                                             └──Pattern:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: 82
                                                                └──Desc: Any
                                           └──Expression:
                                              └──Type expr: Variable: 42
                                              └──Desc: Variable
                                                 └──Variable: h
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: var
                                                    └──Type expr: Constructor: s
                                                       └──Type expr: Variable: 44
                                                    └──Type expr: Variable: 42
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: 44
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: var
                                                       └──Type expr: Constructor: s
                                                          └──Type expr: Variable: 44
                                                       └──Type expr: Variable: 42
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Tail
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Constructor: s
                                                                   └──Type expr: Variable: 122
                                                                └──Type expr: Variable: 42
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Constructor: s
                                                                   └──Type expr: Variable: 44
                                                                └──Type expr: Variable: 42
                                                       └──Pattern:
                                                          └──Type expr: Constructor: var
                                                             └──Type expr: Constructor: s
                                                                └──Type expr: Variable: 122
                                                             └──Type expr: Variable: 42
                                                          └──Desc: Variable: n'
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: 44
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Cons
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 116
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: 118
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: 44
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 116
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: 118
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Variable: 116
                                                                └──Desc: Any
                                                             └──Pattern:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: 118
                                                                └──Desc: Variable: t
                                           └──Expression:
                                              └──Type expr: Variable: 42
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: 118
                                                       └──Type expr: Variable: 42
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Constructor: s
                                                                   └──Type expr: Variable: 118
                                                                └──Type expr: Variable: 42
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: 118
                                                                └──Type expr: Variable: 42
                                                          └──Desc: Variable
                                                             └──Variable: get_var
                                                             └──Type expr: Variable: 42
                                                             └──Type expr: Variable: 118
                                                       └──Expression:
                                                          └──Type expr: Constructor: var
                                                             └──Type expr: Constructor: s
                                                                └──Type expr: Variable: 118
                                                             └──Type expr: Variable: 42
                                                          └──Desc: Variable
                                                             └──Variable: n'
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: 118
                                                    └──Desc: Variable
                                                       └──Variable: t |}]