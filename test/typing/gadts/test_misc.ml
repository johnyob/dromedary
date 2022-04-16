open! Import
open Util

let%expect_test "test-1" =
  let str =
    {|
      type 'a t = 
        | Int of int constraint 'a = int
        | Bool of bool constraint 'a = bool
        | Pair of 'b 'c. 'b t * 'c t constraint 'a = 'b * 'c
        | App of 'b. ('b -> 'a) t * 'b t 
        | Abs of 'b 'c. 'b -> 'c constraint 'a = 'b -> 'c
      ;;

      let rec (type 't) eval = 
        fun (t : 't t) ->
          (match t with 
           ( Int n -> n
           | Bool b -> b
           | Pair (t1, t2) ->
              (eval t1, eval t2)
           | App (f, x) ->
              (eval f) (eval x)
           | Abs f -> f 
           )
          : 't)
      ;;

      let (type 't) discern = 
        fun (t : 't t) ->
          match t with
           ( Int _ -> 1
           | Bool _ -> 2
           | Pair _ -> 3
           | App _ -> 4
           | Abs _ -> 5
           )
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
                     └──Constructor name: Int
                     └──Constructor alphas: a
                     └──Constructor type:
                        └──Type expr: Constructor: t
                           └──Type expr: Variable: a
                     └──Constructor argument:
                        └──Constructor betas:
                        └──Type expr: Constructor: int
                     └──Constraint:
                        └──Type expr: Variable: a
                        └──Type expr: Constructor: int
                  └──Constructor declaration:
                     └──Constructor name: Bool
                     └──Constructor alphas: a
                     └──Constructor type:
                        └──Type expr: Constructor: t
                           └──Type expr: Variable: a
                     └──Constructor argument:
                        └──Constructor betas:
                        └──Type expr: Constructor: bool
                     └──Constraint:
                        └──Type expr: Variable: a
                        └──Type expr: Constructor: bool
                  └──Constructor declaration:
                     └──Constructor name: Pair
                     └──Constructor alphas: a
                     └──Constructor type:
                        └──Type expr: Constructor: t
                           └──Type expr: Variable: a
                     └──Constructor argument:
                        └──Constructor betas: b c
                        └──Type expr: Tuple
                           └──Type expr: Constructor: t
                              └──Type expr: Variable: b
                           └──Type expr: Constructor: t
                              └──Type expr: Variable: c
                     └──Constraint:
                        └──Type expr: Variable: a
                        └──Type expr: Tuple
                           └──Type expr: Variable: b
                           └──Type expr: Variable: c
                  └──Constructor declaration:
                     └──Constructor name: App
                     └──Constructor alphas: a
                     └──Constructor type:
                        └──Type expr: Constructor: t
                           └──Type expr: Variable: a
                     └──Constructor argument:
                        └──Constructor betas: b
                        └──Type expr: Tuple
                           └──Type expr: Constructor: t
                              └──Type expr: Arrow
                                 └──Type expr: Variable: b
                                 └──Type expr: Variable: a
                           └──Type expr: Constructor: t
                              └──Type expr: Variable: b
                  └──Constructor declaration:
                     └──Constructor name: Abs
                     └──Constructor alphas: a
                     └──Constructor type:
                        └──Type expr: Constructor: t
                           └──Type expr: Variable: a
                     └──Constructor argument:
                        └──Constructor betas: b c
                        └──Type expr: Arrow
                           └──Type expr: Variable: b
                           └──Type expr: Variable: c
                     └──Constraint:
                        └──Type expr: Variable: a
                        └──Type expr: Arrow
                           └──Type expr: Variable: b
                           └──Type expr: Variable: c
         └──Structure item: Let
            └──Value bindings:
               └──Value binding:
                  └──Variable: eval
                  └──Abstraction:
                     └──Variables: a19963
                     └──Expression:
                        └──Type expr: Arrow
                           └──Type expr: Constructor: t
                              └──Type expr: Variable: a19980
                           └──Type expr: Variable: a19980
                        └──Desc: Function
                           └──Pattern:
                              └──Type expr: Constructor: t
                                 └──Type expr: Variable: a19980
                              └──Desc: Variable: t
                           └──Expression:
                              └──Type expr: Variable: a19980
                              └──Desc: Match
                                 └──Expression:
                                    └──Type expr: Constructor: t
                                       └──Type expr: Variable: a19980
                                    └──Desc: Variable
                                       └──Variable: t
                                 └──Type expr: Constructor: t
                                    └──Type expr: Variable: a19980
                                 └──Cases:
                                    └──Case:
                                       └──Pattern:
                                          └──Type expr: Constructor: t
                                             └──Type expr: Variable: a19980
                                          └──Desc: Construct
                                             └──Constructor description:
                                                └──Name: Int
                                                └──Constructor argument type:
                                                   └──Type expr: Constructor: int
                                                └──Constructor type:
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: a19980
                                             └──Pattern:
                                                └──Type expr: Constructor: int
                                                └──Desc: Variable: n
                                       └──Expression:
                                          └──Type expr: Variable: a19980
                                          └──Desc: Variable
                                             └──Variable: n
                                    └──Case:
                                       └──Pattern:
                                          └──Type expr: Constructor: t
                                             └──Type expr: Variable: a19980
                                          └──Desc: Construct
                                             └──Constructor description:
                                                └──Name: Bool
                                                └──Constructor argument type:
                                                   └──Type expr: Constructor: bool
                                                └──Constructor type:
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: a19980
                                             └──Pattern:
                                                └──Type expr: Constructor: bool
                                                └──Desc: Variable: b
                                       └──Expression:
                                          └──Type expr: Variable: a19980
                                          └──Desc: Variable
                                             └──Variable: b
                                    └──Case:
                                       └──Pattern:
                                          └──Type expr: Constructor: t
                                             └──Type expr: Variable: a19980
                                          └──Desc: Construct
                                             └──Constructor description:
                                                └──Name: Pair
                                                └──Constructor argument type:
                                                   └──Type expr: Tuple
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: a20020
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: a20018
                                                └──Constructor type:
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: a19980
                                             └──Pattern:
                                                └──Type expr: Tuple
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: a20020
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: a20018
                                                └──Desc: Tuple
                                                   └──Pattern:
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: a20020
                                                      └──Desc: Variable: t1
                                                   └──Pattern:
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: a20018
                                                      └──Desc: Variable: t2
                                       └──Expression:
                                          └──Type expr: Variable: a19980
                                          └──Desc: Tuple
                                             └──Expression:
                                                └──Type expr: Variable: a20020
                                                └──Desc: Application
                                                   └──Expression:
                                                      └──Type expr: Arrow
                                                         └──Type expr: Constructor: t
                                                            └──Type expr: Variable: a20020
                                                         └──Type expr: Variable: a20020
                                                      └──Desc: Variable
                                                         └──Variable: eval
                                                         └──Type expr: Variable: a20020
                                                   └──Expression:
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: a20020
                                                      └──Desc: Variable
                                                         └──Variable: t1
                                             └──Expression:
                                                └──Type expr: Variable: a20018
                                                └──Desc: Application
                                                   └──Expression:
                                                      └──Type expr: Arrow
                                                         └──Type expr: Constructor: t
                                                            └──Type expr: Variable: a20018
                                                         └──Type expr: Variable: a20018
                                                      └──Desc: Variable
                                                         └──Variable: eval
                                                         └──Type expr: Variable: a20018
                                                   └──Expression:
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: a20018
                                                      └──Desc: Variable
                                                         └──Variable: t2
                                    └──Case:
                                       └──Pattern:
                                          └──Type expr: Constructor: t
                                             └──Type expr: Variable: a19980
                                          └──Desc: Construct
                                             └──Constructor description:
                                                └──Name: App
                                                └──Constructor argument type:
                                                   └──Type expr: Tuple
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Arrow
                                                            └──Type expr: Variable: a20067
                                                            └──Type expr: Variable: a19980
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: a20067
                                                └──Constructor type:
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: a19980
                                             └──Pattern:
                                                └──Type expr: Tuple
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Arrow
                                                         └──Type expr: Variable: a20067
                                                         └──Type expr: Variable: a19980
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: a20067
                                                └──Desc: Tuple
                                                   └──Pattern:
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Arrow
                                                            └──Type expr: Variable: a20067
                                                            └──Type expr: Variable: a19980
                                                      └──Desc: Variable: f
                                                   └──Pattern:
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: a20067
                                                      └──Desc: Variable: x
                                       └──Expression:
                                          └──Type expr: Variable: a19980
                                          └──Desc: Application
                                             └──Expression:
                                                └──Type expr: Arrow
                                                   └──Type expr: Variable: a20067
                                                   └──Type expr: Variable: a19980
                                                └──Desc: Application
                                                   └──Expression:
                                                      └──Type expr: Arrow
                                                         └──Type expr: Constructor: t
                                                            └──Type expr: Arrow
                                                               └──Type expr: Variable: a20067
                                                               └──Type expr: Variable: a19980
                                                         └──Type expr: Arrow
                                                            └──Type expr: Variable: a20067
                                                            └──Type expr: Variable: a19980
                                                      └──Desc: Variable
                                                         └──Variable: eval
                                                         └──Type expr: Arrow
                                                            └──Type expr: Variable: a20067
                                                            └──Type expr: Variable: a19980
                                                   └──Expression:
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Arrow
                                                            └──Type expr: Variable: a20067
                                                            └──Type expr: Variable: a19980
                                                      └──Desc: Variable
                                                         └──Variable: f
                                             └──Expression:
                                                └──Type expr: Variable: a20067
                                                └──Desc: Application
                                                   └──Expression:
                                                      └──Type expr: Arrow
                                                         └──Type expr: Constructor: t
                                                            └──Type expr: Variable: a20067
                                                         └──Type expr: Variable: a20067
                                                      └──Desc: Variable
                                                         └──Variable: eval
                                                         └──Type expr: Variable: a20067
                                                   └──Expression:
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: a20067
                                                      └──Desc: Variable
                                                         └──Variable: x
                                    └──Case:
                                       └──Pattern:
                                          └──Type expr: Constructor: t
                                             └──Type expr: Variable: a19980
                                          └──Desc: Construct
                                             └──Constructor description:
                                                └──Name: Abs
                                                └──Constructor argument type:
                                                   └──Type expr: Arrow
                                                      └──Type expr: Variable: a20100
                                                      └──Type expr: Variable: a20101
                                                └──Constructor type:
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: a19980
                                             └──Pattern:
                                                └──Type expr: Arrow
                                                   └──Type expr: Variable: a20100
                                                   └──Type expr: Variable: a20101
                                                └──Desc: Variable: f
                                       └──Expression:
                                          └──Type expr: Variable: a19980
                                          └──Desc: Variable
                                             └──Variable: f
         └──Structure item: Let
            └──Value bindings:
               └──Value binding:
                  └──Pattern:
                     └──Type expr: Arrow
                        └──Type expr: Constructor: t
                           └──Type expr: Variable: a20127
                        └──Type expr: Constructor: int
                     └──Desc: Variable: discern
                  └──Abstraction:
                     └──Variables: a20127
                     └──Expression:
                        └──Type expr: Arrow
                           └──Type expr: Constructor: t
                              └──Type expr: Variable: a20127
                           └──Type expr: Constructor: int
                        └──Desc: Function
                           └──Pattern:
                              └──Type expr: Constructor: t
                                 └──Type expr: Variable: a20127
                              └──Desc: Variable: t
                           └──Expression:
                              └──Type expr: Constructor: int
                              └──Desc: Match
                                 └──Expression:
                                    └──Type expr: Constructor: t
                                       └──Type expr: Variable: a20127
                                    └──Desc: Variable
                                       └──Variable: t
                                 └──Type expr: Constructor: t
                                    └──Type expr: Variable: a20127
                                 └──Cases:
                                    └──Case:
                                       └──Pattern:
                                          └──Type expr: Constructor: t
                                             └──Type expr: Variable: a20127
                                          └──Desc: Construct
                                             └──Constructor description:
                                                └──Name: Int
                                                └──Constructor argument type:
                                                   └──Type expr: Constructor: int
                                                └──Constructor type:
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: a20127
                                             └──Pattern:
                                                └──Type expr: Constructor: int
                                                └──Desc: Any
                                       └──Expression:
                                          └──Type expr: Constructor: int
                                          └──Desc: Constant: 1
                                    └──Case:
                                       └──Pattern:
                                          └──Type expr: Constructor: t
                                             └──Type expr: Variable: a20127
                                          └──Desc: Construct
                                             └──Constructor description:
                                                └──Name: Bool
                                                └──Constructor argument type:
                                                   └──Type expr: Constructor: bool
                                                └──Constructor type:
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: a20127
                                             └──Pattern:
                                                └──Type expr: Constructor: bool
                                                └──Desc: Any
                                       └──Expression:
                                          └──Type expr: Constructor: int
                                          └──Desc: Constant: 2
                                    └──Case:
                                       └──Pattern:
                                          └──Type expr: Constructor: t
                                             └──Type expr: Variable: a20127
                                          └──Desc: Construct
                                             └──Constructor description:
                                                └──Name: Pair
                                                └──Constructor argument type:
                                                   └──Type expr: Tuple
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: a20154
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: a20152
                                                └──Constructor type:
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: a20127
                                             └──Pattern:
                                                └──Type expr: Tuple
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: a20154
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: a20152
                                                └──Desc: Any
                                       └──Expression:
                                          └──Type expr: Constructor: int
                                          └──Desc: Constant: 3
                                    └──Case:
                                       └──Pattern:
                                          └──Type expr: Constructor: t
                                             └──Type expr: Variable: a20127
                                          └──Desc: Construct
                                             └──Constructor description:
                                                └──Name: App
                                                └──Constructor argument type:
                                                   └──Type expr: Tuple
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Arrow
                                                            └──Type expr: Variable: a20171
                                                            └──Type expr: Variable: a20127
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: a20171
                                                └──Constructor type:
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: a20127
                                             └──Pattern:
                                                └──Type expr: Tuple
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Arrow
                                                         └──Type expr: Variable: a20171
                                                         └──Type expr: Variable: a20127
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: a20171
                                                └──Desc: Any
                                       └──Expression:
                                          └──Type expr: Constructor: int
                                          └──Desc: Constant: 4
                                    └──Case:
                                       └──Pattern:
                                          └──Type expr: Constructor: t
                                             └──Type expr: Variable: a20127
                                          └──Desc: Construct
                                             └──Constructor description:
                                                └──Name: Abs
                                                └──Constructor argument type:
                                                   └──Type expr: Arrow
                                                      └──Type expr: Variable: a20180
                                                      └──Type expr: Variable: a20181
                                                └──Constructor type:
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: a20127
                                             └──Pattern:
                                                └──Type expr: Arrow
                                                   └──Type expr: Variable: a20180
                                                   └──Type expr: Variable: a20181
                                                └──Desc: Any
                                       └──Expression:
                                          └──Type expr: Constructor: int
                                          └──Desc: Constant: 5 |}]

let%expect_test "test-2" =
  let str = 
    {|
      type zero;;
      type 'a t =
        | Nil constraint 'a = zero
        | Cons of 'b 'c. 'b * 'c t constraint 'a = 'b * 'c
      ;;

      (* requires annotation bcs rigid equations *)
      let (type 'a 't) head = 
        fun (Cons (x, _) : ('a * 't) t) -> x
      ;;

      let (type 'a 't) tail = 
        fun (Cons (_, t) : ('a * 't) t) -> t 
      ;;

      let rec (type 'a) length = 
        fun (t : 'a t) ->
          (match t with
           ( Nil -> 0
           | Cons (_, t) -> 1 + length t
           )
          : int)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: zero
             └──Type declaration kind: Abstract
       └──Structure item: Type
          └──Type declaration:
             └──Type name: t
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: zero
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas: b c
                      └──Type expr: Tuple
                         └──Type expr: Variable: b
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: c
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Tuple
                         └──Type expr: Variable: b
                         └──Type expr: Variable: c
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Tuple
                            └──Type expr: Variable: a20209
                            └──Type expr: Variable: a20210
                      └──Type expr: Variable: a20212
                   └──Desc: Variable: head
                └──Abstraction:
                   └──Variables: a20209,a20210,a20212,a20212
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Tuple
                               └──Type expr: Variable: a20209
                               └──Type expr: Variable: a20210
                         └──Type expr: Variable: a20212
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Tuple
                                  └──Type expr: Variable: a20209
                                  └──Type expr: Variable: a20210
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Cons
                                  └──Constructor argument type:
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a20212
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: a20214
                                  └──Constructor type:
                                     └──Type expr: Constructor: t
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a20209
                                           └──Type expr: Variable: a20210
                               └──Pattern:
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: a20212
                                     └──Type expr: Constructor: t
                                        └──Type expr: Variable: a20214
                                  └──Desc: Tuple
                                     └──Pattern:
                                        └──Type expr: Variable: a20212
                                        └──Desc: Variable: x
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: a20214
                                        └──Desc: Any
                         └──Expression:
                            └──Type expr: Variable: a20212
                            └──Desc: Variable
                               └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Tuple
                            └──Type expr: Variable: a20244
                            └──Type expr: Variable: a20245
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a20249
                   └──Desc: Variable: tail
                └──Abstraction:
                   └──Variables: a20244,a20245
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Tuple
                               └──Type expr: Variable: a20244
                               └──Type expr: Variable: a20245
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a20249
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Tuple
                                  └──Type expr: Variable: a20244
                                  └──Type expr: Variable: a20245
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Cons
                                  └──Constructor argument type:
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a20247
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: a20249
                                  └──Constructor type:
                                     └──Type expr: Constructor: t
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a20244
                                           └──Type expr: Variable: a20245
                               └──Pattern:
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: a20247
                                     └──Type expr: Constructor: t
                                        └──Type expr: Variable: a20249
                                  └──Desc: Tuple
                                     └──Pattern:
                                        └──Type expr: Variable: a20247
                                        └──Desc: Any
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: a20249
                                        └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: a20249
                            └──Desc: Variable
                               └──Variable: t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: length
                └──Abstraction:
                   └──Variables: a20265
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a20283
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: a20283
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: a20283
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: a20283
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: a20283
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Nil
                                              └──Constructor type:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: a20283
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 0
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: a20283
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Cons
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a20307
                                                    └──Type expr: Constructor: t
                                                       └──Type expr: Variable: a20309
                                              └──Constructor type:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: a20283
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a20307
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: a20309
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Variable: a20307
                                                    └──Desc: Any
                                                 └──Pattern:
                                                    └──Type expr: Constructor: t
                                                       └──Type expr: Variable: a20309
                                                    └──Desc: Variable: t
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: int
                                                          └──Type expr: Constructor: int
                                                    └──Desc: Primitive: (+)
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 1
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a20309
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: length
                                                       └──Type expr: Variable: a20309
                                                 └──Expression:
                                                    └──Type expr: Constructor: t
                                                       └──Type expr: Variable: a20309
                                                    └──Desc: Variable
                                                       └──Variable: t |}]

let%expect_test "test-3" =
  let str = 
    {|
      type 'a u = 
        | C1 of int constraint 'a = int
        | C2 of bool constraint 'a = bool
      ;;

      type 'a v =
        | C3 of int constraint 'a = int
      ;;

      let (type 'a) unexhaustive = 
        fun (t : 'a u) -> 
          (match t with
           ( C2 x -> x)
          : 'a) 
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: u
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: C1
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: u
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: int
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: int
                └──Constructor declaration:
                   └──Constructor name: C2
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: u
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: bool
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: bool
       └──Structure item: Type
          └──Type declaration:
             └──Type name: v
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: C3
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: v
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: int
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: int
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: u
                         └──Type expr: Variable: a20357
                      └──Type expr: Variable: a20357
                   └──Desc: Variable: unexhaustive
                └──Abstraction:
                   └──Variables: a20357
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: u
                            └──Type expr: Variable: a20357
                         └──Type expr: Variable: a20357
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: u
                               └──Type expr: Variable: a20357
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Variable: a20357
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: u
                                     └──Type expr: Variable: a20357
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: u
                                  └──Type expr: Variable: a20357
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: u
                                           └──Type expr: Variable: a20357
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: C2
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: bool
                                              └──Constructor type:
                                                 └──Type expr: Constructor: u
                                                    └──Type expr: Variable: a20357
                                           └──Pattern:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: a20357
                                        └──Desc: Variable
                                           └──Variable: x |}]

let%expect_test "test-4" =
  let str = 
    {|
      type t = int;;
      type u = bool;;
      type 'a v = 
        | Foo of t constraint 'a = t
        | Bar of u constraint 'a = u
      ;;

      let (type 's) same_type = 
        fun (t1 : 's v) (t2 : 's v) ->
          (match (t1, t2) with
           ( (Foo _, Foo _) -> true
           | (Bar _, Bar _) -> true
           ) 
          : bool) 
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
                   └──Alias alphas:
                   └──Type expr: Constructor: int
       └──Structure item: Type
          └──Type declaration:
             └──Type name: u
             └──Type declaration kind: Alias
                └──Alias
                   └──Alias name: u
                   └──Alias alphas:
                   └──Type expr: Constructor: bool
       └──Structure item: Type
          └──Type declaration:
             └──Type name: v
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Foo
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: v
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: t
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: t
                └──Constructor declaration:
                   └──Constructor name: Bar
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: v
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: u
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: u
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: v
                         └──Type expr: Variable: a20385
                      └──Type expr: Arrow
                         └──Type expr: Constructor: v
                            └──Type expr: Variable: a20385
                         └──Type expr: Constructor: bool
                   └──Desc: Variable: same_type
                └──Abstraction:
                   └──Variables: a20385
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: v
                            └──Type expr: Variable: a20385
                         └──Type expr: Arrow
                            └──Type expr: Constructor: v
                               └──Type expr: Variable: a20385
                            └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: v
                               └──Type expr: Variable: a20385
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: v
                                  └──Type expr: Variable: a20385
                               └──Type expr: Constructor: bool
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: v
                                     └──Type expr: Variable: a20385
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: v
                                              └──Type expr: Variable: a20385
                                           └──Type expr: Constructor: v
                                              └──Type expr: Variable: a20385
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: v
                                                 └──Type expr: Variable: a20385
                                              └──Desc: Variable
                                                 └──Variable: t1
                                           └──Expression:
                                              └──Type expr: Constructor: v
                                                 └──Type expr: Variable: a20385
                                              └──Desc: Variable
                                                 └──Variable: t2
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: v
                                           └──Type expr: Variable: a20385
                                        └──Type expr: Constructor: v
                                           └──Type expr: Variable: a20385
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: v
                                                    └──Type expr: Variable: a20385
                                                 └──Type expr: Constructor: v
                                                    └──Type expr: Variable: a20385
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: v
                                                       └──Type expr: Variable: a20385
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Foo
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: t
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: v
                                                                └──Type expr: Variable: a20385
                                                       └──Pattern:
                                                          └──Type expr: Constructor: t
                                                          └──Desc: Any
                                                 └──Pattern:
                                                    └──Type expr: Constructor: v
                                                       └──Type expr: Variable: a20385
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Foo
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: t
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: v
                                                                └──Type expr: Variable: a20385
                                                       └──Pattern:
                                                          └──Type expr: Constructor: t
                                                          └──Desc: Any
                                           └──Expression:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Constant: true
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: v
                                                    └──Type expr: Variable: a20385
                                                 └──Type expr: Constructor: v
                                                    └──Type expr: Variable: a20385
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: v
                                                       └──Type expr: Variable: a20385
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Bar
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: u
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: v
                                                                └──Type expr: Variable: a20385
                                                       └──Pattern:
                                                          └──Type expr: Constructor: u
                                                          └──Desc: Any
                                                 └──Pattern:
                                                    └──Type expr: Constructor: v
                                                       └──Type expr: Variable: a20385
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Bar
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: u
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: v
                                                                └──Type expr: Variable: a20385
                                                       └──Pattern:
                                                          └──Type expr: Constructor: u
                                                          └──Desc: Any
                                           └──Expression:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Constant: true |}]

let%expect_test "test-5" =
  let str = 
    {|
      type 'a t = 
        | Int constraint 'a = int
      ;;

      type 'a option = 
        | None
        | Some of 'a
      ;;

      let f = 
        fun (x : bool t option) -> 
          (match x with ( None -> () ))
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
                   └──Constructor name: Int
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: int
       └──Structure item: Type
          └──Type declaration:
             └──Type name: option
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: None
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: a
                └──Constructor declaration:
                   └──Constructor name: Some
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: a
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: option
                         └──Type expr: Constructor: t
                            └──Type expr: Constructor: bool
                      └──Type expr: Constructor: unit
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: option
                            └──Type expr: Constructor: t
                               └──Type expr: Constructor: bool
                         └──Type expr: Constructor: unit
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: option
                               └──Type expr: Constructor: t
                                  └──Type expr: Constructor: bool
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: unit
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Constructor: t
                                        └──Type expr: Constructor: bool
                                  └──Desc: Variable
                                     └──Variable: x
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: t
                                     └──Type expr: Constructor: bool
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: option
                                           └──Type expr: Constructor: t
                                              └──Type expr: Constructor: bool
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: None
                                              └──Constructor type:
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Constructor: t
                                                       └──Type expr: Constructor: bool
                                     └──Expression:
                                        └──Type expr: Constructor: unit
                                        └──Desc: Constant: () |}]

let%expect_test "" =
  let str = 
    {|
      type 'a t = 
        | Int constraint 'a = int
        | Float constraint 'a = float
      ;;
      
      let f = 
        fun (Int : int t) -> 1
      ;;

      (* No exhaustive checking => no error *)
      let g = 
        fun (t : int t) ->
          match t with
          ( Int -> 1
          | _ -> 2
          )
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
                   └──Constructor name: Int
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: int
                └──Constructor declaration:
                   └──Constructor name: Float
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: float
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Constructor: int
                      └──Type expr: Constructor: int
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Constructor: int
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Constructor: int
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Int
                                  └──Constructor type:
                                     └──Type expr: Constructor: t
                                        └──Type expr: Constructor: int
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Constant: 1
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Constructor: int
                      └──Type expr: Constructor: int
                   └──Desc: Variable: g
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Constructor: int
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Constructor: int
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: t
                                  └──Type expr: Constructor: int
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Constructor: int
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Int
                                              └──Constructor type:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Constructor: int
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 1
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Constructor: int
                                        └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 2 |}]

let%expect_test "" =
  let str = 
    {|
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      type empty = { bottom : 'a. 'a };;
      type ('a, 'b) sum = 
        | Left of 'a 
        | Right of 'b
      ;;

      let not_equal = 
        fun (t : ((int, bool) eq, empty) sum) ->
          match t with
          ( Right empty -> empty )
          (* Left eq -> . raises inconsistent equations error *)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: eq
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Refl
                   └──Constructor alphas: a b
                   └──Constructor type:
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Variable: b
       └──Structure item: Type
          └──Type declaration:
             └──Type name: empty
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: bottom
                   └──Label alphas:
                   └──Label betas: a
                   └──Type expr: Variable: a
                   └──Type expr: Constructor: empty
       └──Structure item: Type
          └──Type declaration:
             └──Type name: sum
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Left
                   └──Constructor alphas: a b
                   └──Constructor type:
                      └──Type expr: Constructor: sum
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: a
                └──Constructor declaration:
                   └──Constructor name: Right
                   └──Constructor alphas: a b
                   └──Constructor type:
                      └──Type expr: Constructor: sum
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: b
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: sum
                         └──Type expr: Constructor: eq
                            └──Type expr: Constructor: int
                            └──Type expr: Constructor: bool
                         └──Type expr: Constructor: empty
                      └──Type expr: Constructor: empty
                   └──Desc: Variable: not_equal
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: sum
                            └──Type expr: Constructor: eq
                               └──Type expr: Constructor: int
                               └──Type expr: Constructor: bool
                            └──Type expr: Constructor: empty
                         └──Type expr: Constructor: empty
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: sum
                               └──Type expr: Constructor: eq
                                  └──Type expr: Constructor: int
                                  └──Type expr: Constructor: bool
                               └──Type expr: Constructor: empty
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: empty
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: sum
                                     └──Type expr: Constructor: eq
                                        └──Type expr: Constructor: int
                                        └──Type expr: Constructor: bool
                                     └──Type expr: Constructor: empty
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: sum
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: bool
                                  └──Type expr: Constructor: empty
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: sum
                                           └──Type expr: Constructor: eq
                                              └──Type expr: Constructor: int
                                              └──Type expr: Constructor: bool
                                           └──Type expr: Constructor: empty
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Right
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: empty
                                              └──Constructor type:
                                                 └──Type expr: Constructor: sum
                                                    └──Type expr: Constructor: eq
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Constructor: bool
                                                    └──Type expr: Constructor: empty
                                           └──Pattern:
                                              └──Type expr: Constructor: empty
                                              └──Desc: Variable: empty
                                     └──Expression:
                                        └──Type expr: Constructor: empty
                                        └──Desc: Variable
                                           └──Variable: empty |}]

let%expect_test "" =
  let str = 
    {|
      type ('a, 'b) ctx = 
        | Nil constraint 'a = unit and 'b = unit
        | Cons of 'c 'd. ('c, 'd) ctx constraint 'a = 'c * unit and 'b = 'd * unit
      ;;

      type 'a var = 
        | Zero of 'b. unit constraint 'a = 'b * unit
        | Succ of 'b. 'b var constraint 'a = 'b * unit
      ;;

      let rec (type 'g1 'g2) f = 
        fun (ctx : ('g1, 'g2) ctx) (v : 'g1 var) ->
          (match (ctx, v) with
           ( (Cons ctx, Zero ()) -> Zero ()
           | (Cons ctx, Succ v) -> Succ (f ctx v) 
           )
          : 'g2 var)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: ctx
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: a b
                   └──Constructor type:
                      └──Type expr: Constructor: ctx
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: unit
                   └──Constraint:
                      └──Type expr: Variable: b
                      └──Type expr: Constructor: unit
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: a b
                   └──Constructor type:
                      └──Type expr: Constructor: ctx
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                   └──Constructor argument:
                      └──Constructor betas: c d
                      └──Type expr: Constructor: ctx
                         └──Type expr: Variable: c
                         └──Type expr: Variable: d
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Tuple
                         └──Type expr: Variable: c
                         └──Type expr: Constructor: unit
                   └──Constraint:
                      └──Type expr: Variable: b
                      └──Type expr: Tuple
                         └──Type expr: Variable: d
                         └──Type expr: Constructor: unit
       └──Structure item: Type
          └──Type declaration:
             └──Type name: var
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Zero
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: var
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas: b
                      └──Type expr: Constructor: unit
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Tuple
                         └──Type expr: Variable: b
                         └──Type expr: Constructor: unit
                └──Constructor declaration:
                   └──Constructor name: Succ
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: var
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas: b
                      └──Type expr: Constructor: var
                         └──Type expr: Variable: b
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Tuple
                         └──Type expr: Variable: b
                         └──Type expr: Constructor: unit
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: f
                └──Abstraction:
                   └──Variables: a20565,a20564
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ctx
                            └──Type expr: Variable: a20592
                            └──Type expr: Variable: a20593
                         └──Type expr: Arrow
                            └──Type expr: Constructor: var
                               └──Type expr: Variable: a20592
                            └──Type expr: Constructor: var
                               └──Type expr: Variable: a20593
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ctx
                               └──Type expr: Variable: a20592
                               └──Type expr: Variable: a20593
                            └──Desc: Variable: ctx
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: var
                                  └──Type expr: Variable: a20592
                               └──Type expr: Constructor: var
                                  └──Type expr: Variable: a20593
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: var
                                     └──Type expr: Variable: a20592
                                  └──Desc: Variable: v
                               └──Expression:
                                  └──Type expr: Constructor: var
                                     └──Type expr: Variable: a20593
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: ctx
                                              └──Type expr: Variable: a20592
                                              └──Type expr: Variable: a20593
                                           └──Type expr: Constructor: var
                                              └──Type expr: Variable: a20592
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: ctx
                                                 └──Type expr: Variable: a20592
                                                 └──Type expr: Variable: a20593
                                              └──Desc: Variable
                                                 └──Variable: ctx
                                           └──Expression:
                                              └──Type expr: Constructor: var
                                                 └──Type expr: Variable: a20592
                                              └──Desc: Variable
                                                 └──Variable: v
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: ctx
                                           └──Type expr: Variable: a20592
                                           └──Type expr: Variable: a20593
                                        └──Type expr: Constructor: var
                                           └──Type expr: Variable: a20592
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ctx
                                                    └──Type expr: Variable: a20592
                                                    └──Type expr: Variable: a20593
                                                 └──Type expr: Constructor: var
                                                    └──Type expr: Variable: a20592
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ctx
                                                       └──Type expr: Variable: a20592
                                                       └──Type expr: Variable: a20593
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Cons
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: ctx
                                                                └──Type expr: Variable: a20632
                                                                └──Type expr: Variable: a20633
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ctx
                                                                └──Type expr: Variable: a20592
                                                                └──Type expr: Variable: a20593
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ctx
                                                             └──Type expr: Variable: a20632
                                                             └──Type expr: Variable: a20633
                                                          └──Desc: Variable: ctx
                                                 └──Pattern:
                                                    └──Type expr: Constructor: var
                                                       └──Type expr: Variable: a20592
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Variable: a20592
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                           └──Expression:
                                              └──Type expr: Constructor: var
                                                 └──Type expr: Variable: a20593
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Zero
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: unit
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: var
                                                          └──Type expr: Variable: a20593
                                                 └──Expression:
                                                    └──Type expr: Constructor: unit
                                                    └──Desc: Constant: ()
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ctx
                                                    └──Type expr: Variable: a20592
                                                    └──Type expr: Variable: a20593
                                                 └──Type expr: Constructor: var
                                                    └──Type expr: Variable: a20592
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ctx
                                                       └──Type expr: Variable: a20592
                                                       └──Type expr: Variable: a20593
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Cons
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: ctx
                                                                └──Type expr: Variable: a20677
                                                                └──Type expr: Variable: a20678
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ctx
                                                                └──Type expr: Variable: a20592
                                                                └──Type expr: Variable: a20593
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ctx
                                                             └──Type expr: Variable: a20677
                                                             └──Type expr: Variable: a20678
                                                          └──Desc: Variable: ctx
                                                 └──Pattern:
                                                    └──Type expr: Constructor: var
                                                       └──Type expr: Variable: a20592
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Variable: a20674
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Variable: a20592
                                                       └──Pattern:
                                                          └──Type expr: Constructor: var
                                                             └──Type expr: Variable: a20674
                                                          └──Desc: Variable: v
                                           └──Expression:
                                              └──Type expr: Constructor: var
                                                 └──Type expr: Variable: a20593
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Succ
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: var
                                                          └──Type expr: Variable: a20678
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: var
                                                          └──Type expr: Variable: a20593
                                                 └──Expression:
                                                    └──Type expr: Constructor: var
                                                       └──Type expr: Variable: a20678
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Variable: a20674
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Variable: a20678
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ctx
                                                                      └──Type expr: Variable: a20674
                                                                      └──Type expr: Variable: a20678
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: var
                                                                         └──Type expr: Variable: a20674
                                                                      └──Type expr: Constructor: var
                                                                         └──Type expr: Variable: a20678
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                                   └──Type expr: Variable: a20678
                                                                   └──Type expr: Variable: a20674
                                                             └──Expression:
                                                                └──Type expr: Constructor: ctx
                                                                   └──Type expr: Variable: a20674
                                                                   └──Type expr: Variable: a20678
                                                                └──Desc: Variable
                                                                   └──Variable: ctx
                                                       └──Expression:
                                                          └──Type expr: Constructor: var
                                                             └──Type expr: Variable: a20674
                                                          └──Desc: Variable
                                                             └──Variable: v |}]

let%expect_test "" =
  let str = 
    {|
      type 'a value = 
        | String of string constraint 'a = string
        | Float of float constraint 'a = float
        | Any
      ;;

      external print_endline : string -> unit = "%print_endline";;

      let print_string_value = 
        fun (v : string value) ->
          (match v with (String s -> print_endline s))
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: value
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: String
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: value
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: string
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: string
                └──Constructor declaration:
                   └──Constructor name: Float
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: value
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: float
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: float
                └──Constructor declaration:
                   └──Constructor name: Any
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: value
                         └──Type expr: Variable: a
       └──Structure item: Primitive
          └──Value description:
             └──Name: print_endline
             └──Scheme:
                └──Variables:
                └──Type expr: Arrow
                   └──Type expr: Constructor: string
                   └──Type expr: Constructor: unit
             └──Primitive name: %print_endline
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: value
                         └──Type expr: Constructor: string
                      └──Type expr: Constructor: unit
                   └──Desc: Variable: print_string_value
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: value
                            └──Type expr: Constructor: string
                         └──Type expr: Constructor: unit
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: value
                               └──Type expr: Constructor: string
                            └──Desc: Variable: v
                         └──Expression:
                            └──Type expr: Constructor: unit
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: value
                                     └──Type expr: Constructor: string
                                  └──Desc: Variable
                                     └──Variable: v
                               └──Type expr: Constructor: value
                                  └──Type expr: Constructor: string
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: value
                                           └──Type expr: Constructor: string
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: String
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: string
                                              └──Constructor type:
                                                 └──Type expr: Constructor: value
                                                    └──Type expr: Constructor: string
                                           └──Pattern:
                                              └──Type expr: Constructor: string
                                              └──Desc: Variable: s
                                     └──Expression:
                                        └──Type expr: Constructor: unit
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: string
                                                 └──Type expr: Constructor: unit
                                              └──Desc: Variable
                                                 └──Variable: print_endline
                                           └──Expression:
                                              └──Type expr: Constructor: string
                                              └──Desc: Variable
                                                 └──Variable: s |}]

let%expect_test "" =
  let str = 
    {|
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      let (type 'a) f = 
        fun (t : ('a, 'a * 'a) eq) ->
          match t with (Refl -> ())
      ;; 
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: eq
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Refl
                   └──Constructor alphas: a b
                   └──Constructor type:
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: a
                         └──Type expr: Variable: b
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Variable: b
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: a20779
                         └──Type expr: Tuple
                            └──Type expr: Variable: a20779
                            └──Type expr: Variable: a20779
                      └──Type expr: Constructor: unit
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: a20779
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: a20779
                            └──Type expr: Tuple
                               └──Type expr: Variable: a20779
                               └──Type expr: Variable: a20779
                         └──Type expr: Constructor: unit
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: a20779
                               └──Type expr: Tuple
                                  └──Type expr: Variable: a20779
                                  └──Type expr: Variable: a20779
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: unit
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: a20779
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a20779
                                        └──Type expr: Variable: a20779
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: a20779
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: a20779
                                     └──Type expr: Variable: a20779
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: a20779
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a20779
                                              └──Type expr: Variable: a20779
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Refl
                                              └──Constructor type:
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: a20779
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a20779
                                                       └──Type expr: Variable: a20779
                                     └──Expression:
                                        └──Type expr: Constructor: unit
                                        └──Desc: Constant: () |}]

let%expect_test "" =
  let str = 
    {|
      type 'a t =
        | Int of int constraint 'a = int
        | Bool of bool constraint 'a = bool
      ;;

      let (type 's) check = 
        fun (t : 's t) ->
          (match t with 
           ( Int n -> n 
           | Bool b -> b
           )
          : 's)
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
                   └──Constructor name: Int
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: int
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: int
                └──Constructor declaration:
                   └──Constructor name: Bool
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: bool
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: bool
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a20803
                      └──Type expr: Variable: a20803
                   └──Desc: Variable: check
                └──Abstraction:
                   └──Variables: a20803
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a20803
                         └──Type expr: Variable: a20803
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: a20803
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Variable: a20803
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: a20803
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: a20803
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: a20803
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Int
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: int
                                              └──Constructor type:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: a20803
                                           └──Pattern:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable: n
                                     └──Expression:
                                        └──Type expr: Variable: a20803
                                        └──Desc: Variable
                                           └──Variable: n
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: a20803
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Bool
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: bool
                                              └──Constructor type:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: a20803
                                           └──Pattern:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Variable: b
                                     └──Expression:
                                        └──Type expr: Variable: a20803
                                        └──Desc: Variable
                                           └──Variable: b |}]

let%expect_test "" =
  let str = 
    {|  
      type 'a t =
        | Int of int constraint 'a = int
        | Bool of bool constraint 'a = bool
      ;;

      let (type 's) check = 
        fun (t : 's t) ->
          (let r = 
            (match t with
             ( Int n -> (n : 's)
             | Bool b -> b
             ))
          in r : 's)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {| ("Type escape it's equational scope" (type_expr ((desc (Ttyp_var a282))))) |}]

let%expect_test "" =
  let str = 
    {|
      type a = A;;
      type b = B;;

      let f = 
        fun t ->
          match t with
          ( A -> 1
          | B -> 2
          )
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    ("Cannot unify types" (type_expr1 ((desc (Ttyp_constr (() b)))))
     (type_expr2 ((desc (Ttyp_constr (() a)))))) |}]

let%expect_test "" =
  let str = 
    {|
      type 'a t = 
        | Foo constraint 'a = int
      ;;

      let (f : int -> int) = 
        fun t -> 
          match t with ( Foo -> 5 )
      ;; 
    |}
  in
  print_infer_result str;
  [%expect {|
    ("Cannot unify types"
     (type_expr1 ((desc (Ttyp_constr ((((desc (Ttyp_var a20898)))) t)))))
     (type_expr2 ((desc (Ttyp_constr (() int)))))) |}]

let%expect_test "" =
  let str = 
    {|
      type 'a t =
        | Int constraint 'a = int
      ;;

      external ignore : 'a. 'a -> unit = "%ignore";;

      let ky = 
        fun x y -> ignore (x = y); x
      ;;

      let (type 'a) test = 
        fun (t : 'a t) ->
          (match t with 
           ( Int -> ky (1 : 'a) 1)
          : 'a) 
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
                   └──Constructor name: Int
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: int
       └──Structure item: Primitive
          └──Value description:
             └──Name: ignore
             └──Scheme:
                └──Variables: a20901
                └──Type expr: Arrow
                   └──Type expr: Variable: a20901
                   └──Type expr: Constructor: unit
             └──Primitive name: %ignore
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: int
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: int
                   └──Desc: Variable: ky
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Constructor: int
                            └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Sequence
                                     └──Expression:
                                        └──Type expr: Constructor: unit
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: bool
                                                 └──Type expr: Constructor: unit
                                              └──Desc: Variable
                                                 └──Variable: ignore
                                                 └──Type expr: Constructor: bool
                                           └──Expression:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Constructor: bool
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: bool
                                                          └──Desc: Primitive: (=)
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: y
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Variable
                                           └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a20948
                      └──Type expr: Variable: a20948
                   └──Desc: Variable: test
                └──Abstraction:
                   └──Variables: a20948
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a20948
                         └──Type expr: Variable: a20948
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: a20948
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Variable: a20948
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: a20948
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: a20948
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: a20948
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Int
                                              └──Constructor type:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: a20948
                                     └──Expression:
                                        └──Type expr: Variable: a20948
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Variable: a20948
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: a20948
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: int
                                                          └──Type expr: Variable: a20948
                                                    └──Desc: Variable
                                                       └──Variable: ky
                                                 └──Expression:
                                                    └──Type expr: Variable: a20948
                                                    └──Desc: Constant: 1
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 1 |}]

let%expect_test "" =
  let str = 
    {|
      type 'a t =
        | Int constraint 'a = int
      ;;

      external ignore : 'a. 'a -> unit = "%ignore";;

      let ky = 
        fun x y -> ignore (x = y); x
      ;;

      let (type 'a) test = 
        fun (t : 'a t) ->
          match t with
          ( Int -> ky (1 : 'a) 1 )
      ;; 
    |}
  in
  print_infer_result str;
  [%expect {| ("Type escape it's equational scope" (type_expr ((desc (Ttyp_var a284))))) |}]

let%expect_test "" =
  let str = 
    {|
      type 'a t =
        | Int constraint 'a = int
      ;;

      external ignore : 'a. 'a -> unit = "%ignore";;

      let ky = 
        fun x y -> ignore (x = y); x
      ;;

      let (type 'a) test = 
        fun (t : 'a t) ->
          (let r = match t with ( Int -> ky (1 : 'a) 1) 
           in r : 'a)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {| ("Type escape it's equational scope" (type_expr ((desc (Ttyp_var a285))))) |}]

let%expect_test "" =
  let str = 
    {|
      type 'a t =
        | Int constraint 'a = int
      ;;

      external ignore : 'a. 'a -> unit = "%ignore";;

      let ky = 
        fun x y -> ignore (x = y); x
      ;;

      let (type 'a) test = 
        fun (x : 'a t) ->
          (let r = match x with (Int -> ky 1 (1 : 'a))
           in r : 'a)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    ("Cannot unify types" (type_expr1 ((desc (Ttyp_var a286))))
     (type_expr2 ((desc (Ttyp_constr (() int)))))) |}]

let%expect_test "" =
  let str = 
    {|
      type 'a t =
        | Int constraint 'a = int
      ;;

      external ignore : 'a. 'a -> unit = "%ignore";;

      let ky = 
        fun x y -> ignore (x = y); x
      ;;

      let (type 'a) test = 
        fun x ->
          let r = match (x : 'a t) with (Int -> ky 1 1) 
          in r
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
                   └──Constructor name: Int
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: int
       └──Structure item: Primitive
          └──Value description:
             └──Name: ignore
             └──Scheme:
                └──Variables: a21212
                └──Type expr: Arrow
                   └──Type expr: Variable: a21212
                   └──Type expr: Constructor: unit
             └──Primitive name: %ignore
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: int
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: int
                   └──Desc: Variable: ky
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Constructor: int
                            └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Sequence
                                     └──Expression:
                                        └──Type expr: Constructor: unit
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: bool
                                                 └──Type expr: Constructor: unit
                                              └──Desc: Variable
                                                 └──Variable: ignore
                                                 └──Type expr: Constructor: bool
                                           └──Expression:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Constructor: bool
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: bool
                                                          └──Desc: Primitive: (=)
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: y
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Variable
                                           └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a21263
                      └──Type expr: Constructor: int
                   └──Desc: Variable: test
                └──Abstraction:
                   └──Variables: a21263
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a21263
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: a21263
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Let
                               └──Value bindings:
                                  └──Value binding:
                                     └──Pattern:
                                        └──Type expr: Constructor: int
                                        └──Desc: Variable: r
                                     └──Abstraction:
                                        └──Variables:
                                        └──Expression:
                                           └──Type expr: Constructor: int
                                           └──Desc: Match
                                              └──Expression:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: a21263
                                                 └──Desc: Variable
                                                    └──Variable: x
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: a21263
                                              └──Cases:
                                                 └──Case:
                                                    └──Pattern:
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a21263
                                                       └──Desc: Construct
                                                          └──Constructor description:
                                                             └──Name: Int
                                                             └──Constructor type:
                                                                └──Type expr: Constructor: t
                                                                   └──Type expr: Variable: a21263
                                                    └──Expression:
                                                       └──Type expr: Constructor: int
                                                       └──Desc: Application
                                                          └──Expression:
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: int
                                                             └──Desc: Application
                                                                └──Expression:
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: int
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: int
                                                                         └──Type expr: Constructor: int
                                                                   └──Desc: Variable
                                                                      └──Variable: ky
                                                                └──Expression:
                                                                   └──Type expr: Constructor: int
                                                                   └──Desc: Constant: 1
                                                          └──Expression:
                                                             └──Type expr: Constructor: int
                                                             └──Desc: Constant: 1
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: r |}]

let%expect_test "" =
  let str = 
    {|
      type 'a t =
        | Int constraint 'a = int
      ;;

      external ignore : 'a. 'a -> unit = "%ignore";;

      let ky = 
        fun x y -> ignore (x = y); x
      ;;

      let (type 'a) test = 
        fun (x : 'a t) ->
          (let r = match x with ( Int -> (1 : 'a) )
           in r 
          : 'a)
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
                   └──Constructor name: Int
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: int
       └──Structure item: Primitive
          └──Value description:
             └──Name: ignore
             └──Scheme:
                └──Variables: a21281
                └──Type expr: Arrow
                   └──Type expr: Variable: a21281
                   └──Type expr: Constructor: unit
             └──Primitive name: %ignore
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: int
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: int
                   └──Desc: Variable: ky
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Constructor: int
                            └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Sequence
                                     └──Expression:
                                        └──Type expr: Constructor: unit
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: bool
                                                 └──Type expr: Constructor: unit
                                              └──Desc: Variable
                                                 └──Variable: ignore
                                                 └──Type expr: Constructor: bool
                                           └──Expression:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Constructor: bool
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: bool
                                                          └──Desc: Primitive: (=)
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: y
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Variable
                                           └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a21328
                      └──Type expr: Variable: a21328
                   └──Desc: Variable: test
                └──Abstraction:
                   └──Variables: a21328
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a21328
                         └──Type expr: Variable: a21328
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: a21328
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: a21328
                            └──Desc: Let
                               └──Value bindings:
                                  └──Value binding:
                                     └──Pattern:
                                        └──Type expr: Variable: a21328
                                        └──Desc: Variable: r
                                     └──Abstraction:
                                        └──Variables:
                                        └──Expression:
                                           └──Type expr: Variable: a21328
                                           └──Desc: Match
                                              └──Expression:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: a21328
                                                 └──Desc: Variable
                                                    └──Variable: x
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: a21328
                                              └──Cases:
                                                 └──Case:
                                                    └──Pattern:
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a21328
                                                       └──Desc: Construct
                                                          └──Constructor description:
                                                             └──Name: Int
                                                             └──Constructor type:
                                                                └──Type expr: Constructor: t
                                                                   └──Type expr: Variable: a21328
                                                    └──Expression:
                                                       └──Type expr: Variable: a21328
                                                       └──Desc: Constant: 1
                               └──Expression:
                                  └──Type expr: Variable: a21328
                                  └──Desc: Variable
                                     └──Variable: r |}]

let%expect_test "" =
  let str = 
    {|
      type 'a t =
        | Int constraint 'a = int
      ;;

      external ignore : 'a. 'a -> unit = "%ignore";;

      let ky = 
        fun x y -> ignore (x = y); x
      ;;

      let (type 'a) test = 
        fun (x : 'a t) ->
          let r = match x with (Int -> 1) in
          r
      ;;

      type 'a option = 
        | None
        | Some of 'a
      ;;

      
      let (type 'a) test2 = 
        fun (x : 'a t) ->
          (let r = ref None in
           (match x with (Int -> r := Some (1 : 'a)));
           !r 
          : 'a option)
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
                   └──Constructor name: Int
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: int
       └──Structure item: Primitive
          └──Value description:
             └──Name: ignore
             └──Scheme:
                └──Variables: a21347
                └──Type expr: Arrow
                   └──Type expr: Variable: a21347
                   └──Type expr: Constructor: unit
             └──Primitive name: %ignore
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: int
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: int
                   └──Desc: Variable: ky
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Constructor: int
                            └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Sequence
                                     └──Expression:
                                        └──Type expr: Constructor: unit
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: bool
                                                 └──Type expr: Constructor: unit
                                              └──Desc: Variable
                                                 └──Variable: ignore
                                                 └──Type expr: Constructor: bool
                                           └──Expression:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Constructor: bool
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: bool
                                                          └──Desc: Primitive: (=)
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: y
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Variable
                                           └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a21394
                      └──Type expr: Constructor: int
                   └──Desc: Variable: test
                └──Abstraction:
                   └──Variables: a21394
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a21394
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: a21394
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Let
                               └──Value bindings:
                                  └──Value binding:
                                     └──Pattern:
                                        └──Type expr: Constructor: int
                                        └──Desc: Variable: r
                                     └──Abstraction:
                                        └──Variables:
                                        └──Expression:
                                           └──Type expr: Constructor: int
                                           └──Desc: Match
                                              └──Expression:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: a21394
                                                 └──Desc: Variable
                                                    └──Variable: x
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: a21394
                                              └──Cases:
                                                 └──Case:
                                                    └──Pattern:
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a21394
                                                       └──Desc: Construct
                                                          └──Constructor description:
                                                             └──Name: Int
                                                             └──Constructor type:
                                                                └──Type expr: Constructor: t
                                                                   └──Type expr: Variable: a21394
                                                    └──Expression:
                                                       └──Type expr: Constructor: int
                                                       └──Desc: Constant: 1
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: r
       └──Structure item: Type
          └──Type declaration:
             └──Type name: option
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: None
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: a
                └──Constructor declaration:
                   └──Constructor name: Some
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: a
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a21415
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: a21415
                   └──Desc: Variable: test2
                └──Abstraction:
                   └──Variables: a21415
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a21415
                         └──Type expr: Constructor: option
                            └──Type expr: Variable: a21415
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: a21415
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: option
                               └──Type expr: Variable: a21415
                            └──Desc: Let
                               └──Value bindings:
                                  └──Value binding:
                                     └──Pattern:
                                        └──Type expr: Constructor: ref
                                           └──Type expr: Constructor: option
                                              └──Type expr: Variable: a21415
                                        └──Desc: Variable: r
                                     └──Abstraction:
                                        └──Variables:
                                        └──Expression:
                                           └──Type expr: Constructor: ref
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Variable: a21415
                                           └──Desc: Application
                                              └──Expression:
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Variable: a21415
                                                    └──Type expr: Constructor: ref
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Variable: a21415
                                                 └──Desc: Primitive: ref
                                              └──Expression:
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Variable: a21415
                                                 └──Desc: Construct
                                                    └──Constructor description:
                                                       └──Name: None
                                                       └──Constructor type:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Variable: a21415
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Variable: a21415
                                  └──Desc: Sequence
                                     └──Expression:
                                        └──Type expr: Constructor: unit
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: a21415
                                              └──Desc: Variable
                                                 └──Variable: x
                                           └──Type expr: Constructor: t
                                              └──Type expr: Variable: a21415
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: t
                                                       └──Type expr: Variable: a21415
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: t
                                                                └──Type expr: Variable: a21415
                                                 └──Expression:
                                                    └──Type expr: Constructor: unit
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Variable: a21415
                                                             └──Type expr: Constructor: unit
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ref
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Variable: a21415
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Variable: a21415
                                                                      └──Type expr: Constructor: unit
                                                                └──Desc: Primitive: (:=)
                                                             └──Expression:
                                                                └──Type expr: Constructor: ref
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Variable: a21415
                                                                └──Desc: Variable
                                                                   └──Variable: r
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Variable: a21415
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Some
                                                                └──Constructor argument type:
                                                                   └──Type expr: Variable: a21415
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Variable: a21415
                                                             └──Expression:
                                                                └──Type expr: Variable: a21415
                                                                └──Desc: Constant: 1
                                     └──Expression:
                                        └──Type expr: Constructor: option
                                           └──Type expr: Variable: a21415
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: ref
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Variable: a21415
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Variable: a21415
                                              └──Desc: Primitive: (!)
                                           └──Expression:
                                              └──Type expr: Constructor: ref
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Variable: a21415
                                              └──Desc: Variable
                                                 └──Variable: r |}]

let%expect_test "" =
  let str = 
    {|
      type 'a t = 
        | Int constraint 'a = int
      ;;

      let either = 
        fun (x : int) (y : int) -> x
      ;;

      let (type 'a) we_y1x = 
        fun (x : 'a) (v : 'a t) ->
          match v with (Int -> let y = either 1 x in y)
      ;;

      (* various equivalent versions of [f], moving the placement of 
         [ignore] -- implementation dependent behavior. *)
      let (type 'a) f = 
        fun (x : 'a t) (y : 'a) ->
          let r = match x with (Int -> (y : 'a)) in
          r
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
                   └──Constructor name: Int
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: int
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: int
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: int
                   └──Desc: Variable: either
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Constructor: int
                            └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: a21499
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a21499
                         └──Type expr: Constructor: int
                   └──Desc: Variable: we_y1x
                └──Abstraction:
                   └──Variables: a21499
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a21499
                         └──Type expr: Arrow
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: a21499
                            └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a21499
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: a21499
                               └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: a21499
                                  └──Desc: Variable: v
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: a21499
                                        └──Desc: Variable
                                           └──Variable: v
                                     └──Type expr: Constructor: t
                                        └──Type expr: Variable: a21499
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: a21499
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Int
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a21499
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Let
                                                 └──Value bindings:
                                                    └──Value binding:
                                                       └──Pattern:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable: y
                                                       └──Abstraction:
                                                          └──Variables:
                                                          └──Expression:
                                                             └──Type expr: Constructor: int
                                                             └──Desc: Application
                                                                └──Expression:
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a21499
                                                                      └──Type expr: Constructor: int
                                                                   └──Desc: Application
                                                                      └──Expression:
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: int
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Variable: a21499
                                                                               └──Type expr: Constructor: int
                                                                         └──Desc: Variable
                                                                            └──Variable: either
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: int
                                                                         └──Desc: Constant: 1
                                                                └──Expression:
                                                                   └──Type expr: Variable: a21499
                                                                   └──Desc: Variable
                                                                      └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: y
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a21544
                      └──Type expr: Arrow
                         └──Type expr: Variable: a21544
                         └──Type expr: Variable: a21544
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: a21544
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a21544
                         └──Type expr: Arrow
                            └──Type expr: Variable: a21544
                            └──Type expr: Variable: a21544
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: a21544
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a21544
                               └──Type expr: Variable: a21544
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: a21544
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Variable: a21544
                                  └──Desc: Let
                                     └──Value bindings:
                                        └──Value binding:
                                           └──Pattern:
                                              └──Type expr: Variable: a21544
                                              └──Desc: Variable: r
                                           └──Abstraction:
                                              └──Variables:
                                              └──Expression:
                                                 └──Type expr: Variable: a21544
                                                 └──Desc: Match
                                                    └──Expression:
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a21544
                                                       └──Desc: Variable
                                                          └──Variable: x
                                                    └──Type expr: Constructor: t
                                                       └──Type expr: Variable: a21544
                                                    └──Cases:
                                                       └──Case:
                                                          └──Pattern:
                                                             └──Type expr: Constructor: t
                                                                └──Type expr: Variable: a21544
                                                             └──Desc: Construct
                                                                └──Constructor description:
                                                                   └──Name: Int
                                                                   └──Constructor type:
                                                                      └──Type expr: Constructor: t
                                                                         └──Type expr: Variable: a21544
                                                          └──Expression:
                                                             └──Type expr: Variable: a21544
                                                             └──Desc: Variable
                                                                └──Variable: y
                                     └──Expression:
                                        └──Type expr: Variable: a21544
                                        └──Desc: Variable
                                           └──Variable: r |}]

let%expect_test "" =
  let str = 
    {|
      type 'a t = 
        | Int of int constraint 'a = int
      ;;

      let (type 'a) f = 
        fun (x : 'a t) -> 
          (match x with (Int y -> y) : 'a)
      ;;

      
      let g = 
        let () = () in
        forall (type 'a) ->
        fun (x : 'a t) ->
          (match x with (Int y -> y) : 'a)
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
                   └──Constructor name: Int
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: int
                   └──Constraint:
                      └──Type expr: Variable: a
                      └──Type expr: Constructor: int
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a21572
                      └──Type expr: Variable: a21572
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: a21572
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a21572
                         └──Type expr: Variable: a21572
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: a21572
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: a21572
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: a21572
                                  └──Desc: Variable
                                     └──Variable: x
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: a21572
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: a21572
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Int
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: int
                                              └──Constructor type:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: a21572
                                           └──Pattern:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable: y
                                     └──Expression:
                                        └──Type expr: Variable: a21572
                                        └──Desc: Variable
                                           └──Variable: y
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: a21627
                      └──Type expr: Variable: a21627
                   └──Desc: Variable: g
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: a21627
                         └──Type expr: Variable: a21627
                      └──Desc: Let
                         └──Value bindings:
                            └──Value binding:
                               └──Pattern:
                                  └──Type expr: Constructor: unit
                                  └──Desc: Constant: ()
                               └──Abstraction:
                                  └──Variables:
                                  └──Expression:
                                     └──Type expr: Constructor: unit
                                     └──Desc: Constant: ()
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: a21627
                               └──Type expr: Variable: a21627
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: a21606
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Variable: a21606
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: a21606
                                        └──Desc: Variable
                                           └──Variable: x
                                     └──Type expr: Constructor: t
                                        └──Type expr: Variable: a21606
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: a21606
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Int
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: int
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: a21606
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Variable: a21606
                                              └──Desc: Variable
                                                 └──Variable: y |}]