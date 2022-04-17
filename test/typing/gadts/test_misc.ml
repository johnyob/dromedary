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
                     └──Constructor alphas: 20936
                     └──Constructor type:
                        └──Type expr: Constructor: t
                           └──Type expr: Variable: 20936
                     └──Constructor argument:
                        └──Constructor betas:
                        └──Type expr: Constructor: int
                     └──Constraint:
                        └──Type expr: Variable: 20936
                        └──Type expr: Constructor: int
                  └──Constructor declaration:
                     └──Constructor name: Bool
                     └──Constructor alphas: 20936
                     └──Constructor type:
                        └──Type expr: Constructor: t
                           └──Type expr: Variable: 20936
                     └──Constructor argument:
                        └──Constructor betas:
                        └──Type expr: Constructor: bool
                     └──Constraint:
                        └──Type expr: Variable: 20936
                        └──Type expr: Constructor: bool
                  └──Constructor declaration:
                     └──Constructor name: Pair
                     └──Constructor alphas: 20936
                     └──Constructor type:
                        └──Type expr: Constructor: t
                           └──Type expr: Variable: 20936
                     └──Constructor argument:
                        └──Constructor betas: 20944 20943
                        └──Type expr: Tuple
                           └──Type expr: Constructor: t
                              └──Type expr: Variable: 20943
                           └──Type expr: Constructor: t
                              └──Type expr: Variable: 20944
                     └──Constraint:
                        └──Type expr: Variable: 20936
                        └──Type expr: Tuple
                           └──Type expr: Variable: 20943
                           └──Type expr: Variable: 20944
                  └──Constructor declaration:
                     └──Constructor name: App
                     └──Constructor alphas: 20936
                     └──Constructor type:
                        └──Type expr: Constructor: t
                           └──Type expr: Variable: 20936
                     └──Constructor argument:
                        └──Constructor betas: 20950
                        └──Type expr: Tuple
                           └──Type expr: Constructor: t
                              └──Type expr: Arrow
                                 └──Type expr: Variable: 20950
                                 └──Type expr: Variable: 20936
                           └──Type expr: Constructor: t
                              └──Type expr: Variable: 20950
                  └──Constructor declaration:
                     └──Constructor name: Abs
                     └──Constructor alphas: 20936
                     └──Constructor type:
                        └──Type expr: Constructor: t
                           └──Type expr: Variable: 20936
                     └──Constructor argument:
                        └──Constructor betas: 20957 20956
                        └──Type expr: Arrow
                           └──Type expr: Variable: 20956
                           └──Type expr: Variable: 20957
                     └──Constraint:
                        └──Type expr: Variable: 20936
                        └──Type expr: Arrow
                           └──Type expr: Variable: 20956
                           └──Type expr: Variable: 20957
         └──Structure item: Let
            └──Value bindings:
               └──Value binding:
                  └──Variable: eval
                  └──Abstraction:
                     └──Variables: 20965
                     └──Expression:
                        └──Type expr: Arrow
                           └──Type expr: Constructor: t
                              └──Type expr: Variable: 20982
                           └──Type expr: Variable: 20982
                        └──Desc: Function
                           └──Pattern:
                              └──Type expr: Constructor: t
                                 └──Type expr: Variable: 20982
                              └──Desc: Variable: t
                           └──Expression:
                              └──Type expr: Variable: 20982
                              └──Desc: Match
                                 └──Expression:
                                    └──Type expr: Constructor: t
                                       └──Type expr: Variable: 20982
                                    └──Desc: Variable
                                       └──Variable: t
                                 └──Type expr: Constructor: t
                                    └──Type expr: Variable: 20982
                                 └──Cases:
                                    └──Case:
                                       └──Pattern:
                                          └──Type expr: Constructor: t
                                             └──Type expr: Variable: 20982
                                          └──Desc: Construct
                                             └──Constructor description:
                                                └──Name: Int
                                                └──Constructor argument type:
                                                   └──Type expr: Constructor: int
                                                └──Constructor type:
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: 20982
                                             └──Pattern:
                                                └──Type expr: Constructor: int
                                                └──Desc: Variable: n
                                       └──Expression:
                                          └──Type expr: Variable: 20982
                                          └──Desc: Variable
                                             └──Variable: n
                                    └──Case:
                                       └──Pattern:
                                          └──Type expr: Constructor: t
                                             └──Type expr: Variable: 20982
                                          └──Desc: Construct
                                             └──Constructor description:
                                                └──Name: Bool
                                                └──Constructor argument type:
                                                   └──Type expr: Constructor: bool
                                                └──Constructor type:
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: 20982
                                             └──Pattern:
                                                └──Type expr: Constructor: bool
                                                └──Desc: Variable: b
                                       └──Expression:
                                          └──Type expr: Variable: 20982
                                          └──Desc: Variable
                                             └──Variable: b
                                    └──Case:
                                       └──Pattern:
                                          └──Type expr: Constructor: t
                                             └──Type expr: Variable: 20982
                                          └──Desc: Construct
                                             └──Constructor description:
                                                └──Name: Pair
                                                └──Constructor argument type:
                                                   └──Type expr: Tuple
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: 21022
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: 21020
                                                └──Constructor type:
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: 20982
                                             └──Pattern:
                                                └──Type expr: Tuple
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: 21022
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: 21020
                                                └──Desc: Tuple
                                                   └──Pattern:
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: 21022
                                                      └──Desc: Variable: t1
                                                   └──Pattern:
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: 21020
                                                      └──Desc: Variable: t2
                                       └──Expression:
                                          └──Type expr: Variable: 20982
                                          └──Desc: Tuple
                                             └──Expression:
                                                └──Type expr: Variable: 21022
                                                └──Desc: Application
                                                   └──Expression:
                                                      └──Type expr: Arrow
                                                         └──Type expr: Constructor: t
                                                            └──Type expr: Variable: 21022
                                                         └──Type expr: Variable: 21022
                                                      └──Desc: Variable
                                                         └──Variable: eval
                                                         └──Type expr: Variable: 21022
                                                   └──Expression:
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: 21022
                                                      └──Desc: Variable
                                                         └──Variable: t1
                                             └──Expression:
                                                └──Type expr: Variable: 21020
                                                └──Desc: Application
                                                   └──Expression:
                                                      └──Type expr: Arrow
                                                         └──Type expr: Constructor: t
                                                            └──Type expr: Variable: 21020
                                                         └──Type expr: Variable: 21020
                                                      └──Desc: Variable
                                                         └──Variable: eval
                                                         └──Type expr: Variable: 21020
                                                   └──Expression:
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: 21020
                                                      └──Desc: Variable
                                                         └──Variable: t2
                                    └──Case:
                                       └──Pattern:
                                          └──Type expr: Constructor: t
                                             └──Type expr: Variable: 20982
                                          └──Desc: Construct
                                             └──Constructor description:
                                                └──Name: App
                                                └──Constructor argument type:
                                                   └──Type expr: Tuple
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Arrow
                                                            └──Type expr: Variable: 21069
                                                            └──Type expr: Variable: 20982
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: 21069
                                                └──Constructor type:
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: 20982
                                             └──Pattern:
                                                └──Type expr: Tuple
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Arrow
                                                         └──Type expr: Variable: 21069
                                                         └──Type expr: Variable: 20982
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: 21069
                                                └──Desc: Tuple
                                                   └──Pattern:
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Arrow
                                                            └──Type expr: Variable: 21069
                                                            └──Type expr: Variable: 20982
                                                      └──Desc: Variable: f
                                                   └──Pattern:
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: 21069
                                                      └──Desc: Variable: x
                                       └──Expression:
                                          └──Type expr: Variable: 20982
                                          └──Desc: Application
                                             └──Expression:
                                                └──Type expr: Arrow
                                                   └──Type expr: Variable: 21069
                                                   └──Type expr: Variable: 20982
                                                └──Desc: Application
                                                   └──Expression:
                                                      └──Type expr: Arrow
                                                         └──Type expr: Constructor: t
                                                            └──Type expr: Arrow
                                                               └──Type expr: Variable: 21069
                                                               └──Type expr: Variable: 20982
                                                         └──Type expr: Arrow
                                                            └──Type expr: Variable: 21069
                                                            └──Type expr: Variable: 20982
                                                      └──Desc: Variable
                                                         └──Variable: eval
                                                         └──Type expr: Arrow
                                                            └──Type expr: Variable: 21069
                                                            └──Type expr: Variable: 20982
                                                   └──Expression:
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Arrow
                                                            └──Type expr: Variable: 21069
                                                            └──Type expr: Variable: 20982
                                                      └──Desc: Variable
                                                         └──Variable: f
                                             └──Expression:
                                                └──Type expr: Variable: 21069
                                                └──Desc: Application
                                                   └──Expression:
                                                      └──Type expr: Arrow
                                                         └──Type expr: Constructor: t
                                                            └──Type expr: Variable: 21069
                                                         └──Type expr: Variable: 21069
                                                      └──Desc: Variable
                                                         └──Variable: eval
                                                         └──Type expr: Variable: 21069
                                                   └──Expression:
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: 21069
                                                      └──Desc: Variable
                                                         └──Variable: x
                                    └──Case:
                                       └──Pattern:
                                          └──Type expr: Constructor: t
                                             └──Type expr: Variable: 20982
                                          └──Desc: Construct
                                             └──Constructor description:
                                                └──Name: Abs
                                                └──Constructor argument type:
                                                   └──Type expr: Arrow
                                                      └──Type expr: Variable: 21102
                                                      └──Type expr: Variable: 21103
                                                └──Constructor type:
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: 20982
                                             └──Pattern:
                                                └──Type expr: Arrow
                                                   └──Type expr: Variable: 21102
                                                   └──Type expr: Variable: 21103
                                                └──Desc: Variable: f
                                       └──Expression:
                                          └──Type expr: Variable: 20982
                                          └──Desc: Variable
                                             └──Variable: f
         └──Structure item: Let
            └──Value bindings:
               └──Value binding:
                  └──Pattern:
                     └──Type expr: Arrow
                        └──Type expr: Constructor: t
                           └──Type expr: Variable: 21129
                        └──Type expr: Constructor: int
                     └──Desc: Variable: discern
                  └──Abstraction:
                     └──Variables: 21129
                     └──Expression:
                        └──Type expr: Arrow
                           └──Type expr: Constructor: t
                              └──Type expr: Variable: 21129
                           └──Type expr: Constructor: int
                        └──Desc: Function
                           └──Pattern:
                              └──Type expr: Constructor: t
                                 └──Type expr: Variable: 21129
                              └──Desc: Variable: t
                           └──Expression:
                              └──Type expr: Constructor: int
                              └──Desc: Match
                                 └──Expression:
                                    └──Type expr: Constructor: t
                                       └──Type expr: Variable: 21129
                                    └──Desc: Variable
                                       └──Variable: t
                                 └──Type expr: Constructor: t
                                    └──Type expr: Variable: 21129
                                 └──Cases:
                                    └──Case:
                                       └──Pattern:
                                          └──Type expr: Constructor: t
                                             └──Type expr: Variable: 21129
                                          └──Desc: Construct
                                             └──Constructor description:
                                                └──Name: Int
                                                └──Constructor argument type:
                                                   └──Type expr: Constructor: int
                                                └──Constructor type:
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: 21129
                                             └──Pattern:
                                                └──Type expr: Constructor: int
                                                └──Desc: Any
                                       └──Expression:
                                          └──Type expr: Constructor: int
                                          └──Desc: Constant: 1
                                    └──Case:
                                       └──Pattern:
                                          └──Type expr: Constructor: t
                                             └──Type expr: Variable: 21129
                                          └──Desc: Construct
                                             └──Constructor description:
                                                └──Name: Bool
                                                └──Constructor argument type:
                                                   └──Type expr: Constructor: bool
                                                └──Constructor type:
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: 21129
                                             └──Pattern:
                                                └──Type expr: Constructor: bool
                                                └──Desc: Any
                                       └──Expression:
                                          └──Type expr: Constructor: int
                                          └──Desc: Constant: 2
                                    └──Case:
                                       └──Pattern:
                                          └──Type expr: Constructor: t
                                             └──Type expr: Variable: 21129
                                          └──Desc: Construct
                                             └──Constructor description:
                                                └──Name: Pair
                                                └──Constructor argument type:
                                                   └──Type expr: Tuple
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: 21156
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: 21154
                                                └──Constructor type:
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: 21129
                                             └──Pattern:
                                                └──Type expr: Tuple
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: 21156
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: 21154
                                                └──Desc: Any
                                       └──Expression:
                                          └──Type expr: Constructor: int
                                          └──Desc: Constant: 3
                                    └──Case:
                                       └──Pattern:
                                          └──Type expr: Constructor: t
                                             └──Type expr: Variable: 21129
                                          └──Desc: Construct
                                             └──Constructor description:
                                                └──Name: App
                                                └──Constructor argument type:
                                                   └──Type expr: Tuple
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Arrow
                                                            └──Type expr: Variable: 21173
                                                            └──Type expr: Variable: 21129
                                                      └──Type expr: Constructor: t
                                                         └──Type expr: Variable: 21173
                                                └──Constructor type:
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: 21129
                                             └──Pattern:
                                                └──Type expr: Tuple
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Arrow
                                                         └──Type expr: Variable: 21173
                                                         └──Type expr: Variable: 21129
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: 21173
                                                └──Desc: Any
                                       └──Expression:
                                          └──Type expr: Constructor: int
                                          └──Desc: Constant: 4
                                    └──Case:
                                       └──Pattern:
                                          └──Type expr: Constructor: t
                                             └──Type expr: Variable: 21129
                                          └──Desc: Construct
                                             └──Constructor description:
                                                └──Name: Abs
                                                └──Constructor argument type:
                                                   └──Type expr: Arrow
                                                      └──Type expr: Variable: 21182
                                                      └──Type expr: Variable: 21183
                                                └──Constructor type:
                                                   └──Type expr: Constructor: t
                                                      └──Type expr: Variable: 21129
                                             └──Pattern:
                                                └──Type expr: Arrow
                                                   └──Type expr: Variable: 21182
                                                   └──Type expr: Variable: 21183
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
                   └──Constructor alphas: 21191
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 21191
                   └──Constraint:
                      └──Type expr: Variable: 21191
                      └──Type expr: Constructor: zero
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 21191
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 21191
                   └──Constructor argument:
                      └──Constructor betas: 21195 21194
                      └──Type expr: Tuple
                         └──Type expr: Variable: 21194
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: 21195
                   └──Constraint:
                      └──Type expr: Variable: 21191
                      └──Type expr: Tuple
                         └──Type expr: Variable: 21194
                         └──Type expr: Variable: 21195
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Tuple
                            └──Type expr: Variable: 21220
                            └──Type expr: Variable: 21221
                      └──Type expr: Variable: 21223
                   └──Desc: Variable: head
                └──Abstraction:
                   └──Variables: 21220,21221,21223,21223
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Tuple
                               └──Type expr: Variable: 21220
                               └──Type expr: Variable: 21221
                         └──Type expr: Variable: 21223
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Tuple
                                  └──Type expr: Variable: 21220
                                  └──Type expr: Variable: 21221
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Cons
                                  └──Constructor argument type:
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: 21223
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: 21225
                                  └──Constructor type:
                                     └──Type expr: Constructor: t
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 21220
                                           └──Type expr: Variable: 21221
                               └──Pattern:
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: 21223
                                     └──Type expr: Constructor: t
                                        └──Type expr: Variable: 21225
                                  └──Desc: Tuple
                                     └──Pattern:
                                        └──Type expr: Variable: 21223
                                        └──Desc: Variable: x
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: 21225
                                        └──Desc: Any
                         └──Expression:
                            └──Type expr: Variable: 21223
                            └──Desc: Variable
                               └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Tuple
                            └──Type expr: Variable: 21255
                            └──Type expr: Variable: 21256
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 21260
                   └──Desc: Variable: tail
                └──Abstraction:
                   └──Variables: 21255,21256
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Tuple
                               └──Type expr: Variable: 21255
                               └──Type expr: Variable: 21256
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: 21260
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Tuple
                                  └──Type expr: Variable: 21255
                                  └──Type expr: Variable: 21256
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Cons
                                  └──Constructor argument type:
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: 21258
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: 21260
                                  └──Constructor type:
                                     └──Type expr: Constructor: t
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 21255
                                           └──Type expr: Variable: 21256
                               └──Pattern:
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: 21258
                                     └──Type expr: Constructor: t
                                        └──Type expr: Variable: 21260
                                  └──Desc: Tuple
                                     └──Pattern:
                                        └──Type expr: Variable: 21258
                                        └──Desc: Any
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: 21260
                                        └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: 21260
                            └──Desc: Variable
                               └──Variable: t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: length
                └──Abstraction:
                   └──Variables: 21276
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: 21294
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: 21294
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: 21294
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: 21294
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: 21294
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Nil
                                              └──Constructor type:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: 21294
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 0
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: 21294
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Cons
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 21318
                                                    └──Type expr: Constructor: t
                                                       └──Type expr: Variable: 21320
                                              └──Constructor type:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: 21294
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: 21318
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: 21320
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Variable: 21318
                                                    └──Desc: Any
                                                 └──Pattern:
                                                    └──Type expr: Constructor: t
                                                       └──Type expr: Variable: 21320
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
                                                          └──Type expr: Variable: 21320
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: length
                                                       └──Type expr: Variable: 21320
                                                 └──Expression:
                                                    └──Type expr: Constructor: t
                                                       └──Type expr: Variable: 21320
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
                   └──Constructor alphas: 21359
                   └──Constructor type:
                      └──Type expr: Constructor: u
                         └──Type expr: Variable: 21359
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: int
                   └──Constraint:
                      └──Type expr: Variable: 21359
                      └──Type expr: Constructor: int
                └──Constructor declaration:
                   └──Constructor name: C2
                   └──Constructor alphas: 21359
                   └──Constructor type:
                      └──Type expr: Constructor: u
                         └──Type expr: Variable: 21359
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: bool
                   └──Constraint:
                      └──Type expr: Variable: 21359
                      └──Type expr: Constructor: bool
       └──Structure item: Type
          └──Type declaration:
             └──Type name: v
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: C3
                   └──Constructor alphas: 21366
                   └──Constructor type:
                      └──Type expr: Constructor: v
                         └──Type expr: Variable: 21366
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: int
                   └──Constraint:
                      └──Type expr: Variable: 21366
                      └──Type expr: Constructor: int
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: u
                         └──Type expr: Variable: 21379
                      └──Type expr: Variable: 21379
                   └──Desc: Variable: unexhaustive
                └──Abstraction:
                   └──Variables: 21379
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: u
                            └──Type expr: Variable: 21379
                         └──Type expr: Variable: 21379
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: u
                               └──Type expr: Variable: 21379
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Variable: 21379
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: u
                                     └──Type expr: Variable: 21379
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: u
                                  └──Type expr: Variable: 21379
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: u
                                           └──Type expr: Variable: 21379
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: C2
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: bool
                                              └──Constructor type:
                                                 └──Type expr: Constructor: u
                                                    └──Type expr: Variable: 21379
                                           └──Pattern:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: 21379
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
                   └──Constructor alphas: 21400
                   └──Constructor type:
                      └──Type expr: Constructor: v
                         └──Type expr: Variable: 21400
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: t
                   └──Constraint:
                      └──Type expr: Variable: 21400
                      └──Type expr: Constructor: t
                └──Constructor declaration:
                   └──Constructor name: Bar
                   └──Constructor alphas: 21400
                   └──Constructor type:
                      └──Type expr: Constructor: v
                         └──Type expr: Variable: 21400
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: u
                   └──Constraint:
                      └──Type expr: Variable: 21400
                      └──Type expr: Constructor: u
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: v
                         └──Type expr: Variable: 21416
                      └──Type expr: Arrow
                         └──Type expr: Constructor: v
                            └──Type expr: Variable: 21416
                         └──Type expr: Constructor: bool
                   └──Desc: Variable: same_type
                └──Abstraction:
                   └──Variables: 21416
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: v
                            └──Type expr: Variable: 21416
                         └──Type expr: Arrow
                            └──Type expr: Constructor: v
                               └──Type expr: Variable: 21416
                            └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: v
                               └──Type expr: Variable: 21416
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: v
                                  └──Type expr: Variable: 21416
                               └──Type expr: Constructor: bool
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: v
                                     └──Type expr: Variable: 21416
                                  └──Desc: Variable: t2
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: v
                                              └──Type expr: Variable: 21416
                                           └──Type expr: Constructor: v
                                              └──Type expr: Variable: 21416
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: v
                                                 └──Type expr: Variable: 21416
                                              └──Desc: Variable
                                                 └──Variable: t1
                                           └──Expression:
                                              └──Type expr: Constructor: v
                                                 └──Type expr: Variable: 21416
                                              └──Desc: Variable
                                                 └──Variable: t2
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: v
                                           └──Type expr: Variable: 21416
                                        └──Type expr: Constructor: v
                                           └──Type expr: Variable: 21416
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: v
                                                    └──Type expr: Variable: 21416
                                                 └──Type expr: Constructor: v
                                                    └──Type expr: Variable: 21416
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: v
                                                       └──Type expr: Variable: 21416
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Foo
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: t
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: v
                                                                └──Type expr: Variable: 21416
                                                       └──Pattern:
                                                          └──Type expr: Constructor: t
                                                          └──Desc: Any
                                                 └──Pattern:
                                                    └──Type expr: Constructor: v
                                                       └──Type expr: Variable: 21416
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Foo
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: t
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: v
                                                                └──Type expr: Variable: 21416
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
                                                    └──Type expr: Variable: 21416
                                                 └──Type expr: Constructor: v
                                                    └──Type expr: Variable: 21416
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: v
                                                       └──Type expr: Variable: 21416
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Bar
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: u
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: v
                                                                └──Type expr: Variable: 21416
                                                       └──Pattern:
                                                          └──Type expr: Constructor: u
                                                          └──Desc: Any
                                                 └──Pattern:
                                                    └──Type expr: Constructor: v
                                                       └──Type expr: Variable: 21416
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Bar
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: u
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: v
                                                                └──Type expr: Variable: 21416
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
                   └──Constructor alphas: 21482
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 21482
                   └──Constraint:
                      └──Type expr: Variable: 21482
                      └──Type expr: Constructor: int
       └──Structure item: Type
          └──Type declaration:
             └──Type name: option
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: None
                   └──Constructor alphas: 21485
                   └──Constructor type:
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: 21485
                └──Constructor declaration:
                   └──Constructor name: Some
                   └──Constructor alphas: 21485
                   └──Constructor type:
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: 21485
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: 21485
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
                   └──Constructor alphas: 21514
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 21514
                   └──Constraint:
                      └──Type expr: Variable: 21514
                      └──Type expr: Constructor: int
                └──Constructor declaration:
                   └──Constructor name: Float
                   └──Constructor alphas: 21514
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 21514
                   └──Constraint:
                      └──Type expr: Variable: 21514
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
                   └──Constructor alphas: 21560 21561
                   └──Constructor type:
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: 21560
                         └──Type expr: Variable: 21561
                   └──Constraint:
                      └──Type expr: Variable: 21560
                      └──Type expr: Variable: 21561
       └──Structure item: Type
          └──Type declaration:
             └──Type name: empty
             └──Type declaration kind: Record
                └──Label declaration:
                   └──Label name: bottom
                   └──Label alphas:
                   └──Label betas: 21563
                   └──Type expr: Variable: 21563
                   └──Type expr: Constructor: empty
       └──Structure item: Type
          └──Type declaration:
             └──Type name: sum
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Left
                   └──Constructor alphas: 21565 21566
                   └──Constructor type:
                      └──Type expr: Constructor: sum
                         └──Type expr: Variable: 21565
                         └──Type expr: Variable: 21566
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: 21565
                └──Constructor declaration:
                   └──Constructor name: Right
                   └──Constructor alphas: 21565 21566
                   └──Constructor type:
                      └──Type expr: Constructor: sum
                         └──Type expr: Variable: 21565
                         └──Type expr: Variable: 21566
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: 21566
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
                   └──Constructor alphas: 21604 21605
                   └──Constructor type:
                      └──Type expr: Constructor: ctx
                         └──Type expr: Variable: 21604
                         └──Type expr: Variable: 21605
                   └──Constraint:
                      └──Type expr: Variable: 21604
                      └──Type expr: Constructor: unit
                   └──Constraint:
                      └──Type expr: Variable: 21605
                      └──Type expr: Constructor: unit
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: 21604 21605
                   └──Constructor type:
                      └──Type expr: Constructor: ctx
                         └──Type expr: Variable: 21604
                         └──Type expr: Variable: 21605
                   └──Constructor argument:
                      └──Constructor betas: 21610 21609
                      └──Type expr: Constructor: ctx
                         └──Type expr: Variable: 21609
                         └──Type expr: Variable: 21610
                   └──Constraint:
                      └──Type expr: Variable: 21604
                      └──Type expr: Tuple
                         └──Type expr: Variable: 21609
                         └──Type expr: Constructor: unit
                   └──Constraint:
                      └──Type expr: Variable: 21605
                      └──Type expr: Tuple
                         └──Type expr: Variable: 21610
                         └──Type expr: Constructor: unit
       └──Structure item: Type
          └──Type declaration:
             └──Type name: var
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Zero
                   └──Constructor alphas: 21617
                   └──Constructor type:
                      └──Type expr: Constructor: var
                         └──Type expr: Variable: 21617
                   └──Constructor argument:
                      └──Constructor betas: 21618
                      └──Type expr: Constructor: unit
                   └──Constraint:
                      └──Type expr: Variable: 21617
                      └──Type expr: Tuple
                         └──Type expr: Variable: 21618
                         └──Type expr: Constructor: unit
                └──Constructor declaration:
                   └──Constructor name: Succ
                   └──Constructor alphas: 21617
                   └──Constructor type:
                      └──Type expr: Constructor: var
                         └──Type expr: Variable: 21617
                   └──Constructor argument:
                      └──Constructor betas: 21623
                      └──Type expr: Constructor: var
                         └──Type expr: Variable: 21623
                   └──Constraint:
                      └──Type expr: Variable: 21617
                      └──Type expr: Tuple
                         └──Type expr: Variable: 21623
                         └──Type expr: Constructor: unit
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: f
                └──Abstraction:
                   └──Variables: 21640,21639
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: ctx
                            └──Type expr: Variable: 21667
                            └──Type expr: Variable: 21668
                         └──Type expr: Arrow
                            └──Type expr: Constructor: var
                               └──Type expr: Variable: 21667
                            └──Type expr: Constructor: var
                               └──Type expr: Variable: 21668
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: ctx
                               └──Type expr: Variable: 21667
                               └──Type expr: Variable: 21668
                            └──Desc: Variable: ctx
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: var
                                  └──Type expr: Variable: 21667
                               └──Type expr: Constructor: var
                                  └──Type expr: Variable: 21668
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: var
                                     └──Type expr: Variable: 21667
                                  └──Desc: Variable: v
                               └──Expression:
                                  └──Type expr: Constructor: var
                                     └──Type expr: Variable: 21668
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: ctx
                                              └──Type expr: Variable: 21667
                                              └──Type expr: Variable: 21668
                                           └──Type expr: Constructor: var
                                              └──Type expr: Variable: 21667
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: ctx
                                                 └──Type expr: Variable: 21667
                                                 └──Type expr: Variable: 21668
                                              └──Desc: Variable
                                                 └──Variable: ctx
                                           └──Expression:
                                              └──Type expr: Constructor: var
                                                 └──Type expr: Variable: 21667
                                              └──Desc: Variable
                                                 └──Variable: v
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: ctx
                                           └──Type expr: Variable: 21667
                                           └──Type expr: Variable: 21668
                                        └──Type expr: Constructor: var
                                           └──Type expr: Variable: 21667
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ctx
                                                    └──Type expr: Variable: 21667
                                                    └──Type expr: Variable: 21668
                                                 └──Type expr: Constructor: var
                                                    └──Type expr: Variable: 21667
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ctx
                                                       └──Type expr: Variable: 21667
                                                       └──Type expr: Variable: 21668
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Cons
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: ctx
                                                                └──Type expr: Variable: 21707
                                                                └──Type expr: Variable: 21708
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ctx
                                                                └──Type expr: Variable: 21667
                                                                └──Type expr: Variable: 21668
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ctx
                                                             └──Type expr: Variable: 21707
                                                             └──Type expr: Variable: 21708
                                                          └──Desc: Variable: ctx
                                                 └──Pattern:
                                                    └──Type expr: Constructor: var
                                                       └──Type expr: Variable: 21667
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Zero
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: unit
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Variable: 21667
                                                       └──Pattern:
                                                          └──Type expr: Constructor: unit
                                                          └──Desc: Constant: ()
                                           └──Expression:
                                              └──Type expr: Constructor: var
                                                 └──Type expr: Variable: 21668
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Zero
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: unit
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: var
                                                          └──Type expr: Variable: 21668
                                                 └──Expression:
                                                    └──Type expr: Constructor: unit
                                                    └──Desc: Constant: ()
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: ctx
                                                    └──Type expr: Variable: 21667
                                                    └──Type expr: Variable: 21668
                                                 └──Type expr: Constructor: var
                                                    └──Type expr: Variable: 21667
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: ctx
                                                       └──Type expr: Variable: 21667
                                                       └──Type expr: Variable: 21668
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Cons
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: ctx
                                                                └──Type expr: Variable: 21752
                                                                └──Type expr: Variable: 21753
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: ctx
                                                                └──Type expr: Variable: 21667
                                                                └──Type expr: Variable: 21668
                                                       └──Pattern:
                                                          └──Type expr: Constructor: ctx
                                                             └──Type expr: Variable: 21752
                                                             └──Type expr: Variable: 21753
                                                          └──Desc: Variable: ctx
                                                 └──Pattern:
                                                    └──Type expr: Constructor: var
                                                       └──Type expr: Variable: 21667
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Succ
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Variable: 21749
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Variable: 21667
                                                       └──Pattern:
                                                          └──Type expr: Constructor: var
                                                             └──Type expr: Variable: 21749
                                                          └──Desc: Variable: v
                                           └──Expression:
                                              └──Type expr: Constructor: var
                                                 └──Type expr: Variable: 21668
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Succ
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: var
                                                          └──Type expr: Variable: 21753
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: var
                                                          └──Type expr: Variable: 21668
                                                 └──Expression:
                                                    └──Type expr: Constructor: var
                                                       └──Type expr: Variable: 21753
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Variable: 21749
                                                             └──Type expr: Constructor: var
                                                                └──Type expr: Variable: 21753
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ctx
                                                                      └──Type expr: Variable: 21749
                                                                      └──Type expr: Variable: 21753
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: var
                                                                         └──Type expr: Variable: 21749
                                                                      └──Type expr: Constructor: var
                                                                         └──Type expr: Variable: 21753
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                                   └──Type expr: Variable: 21753
                                                                   └──Type expr: Variable: 21749
                                                             └──Expression:
                                                                └──Type expr: Constructor: ctx
                                                                   └──Type expr: Variable: 21749
                                                                   └──Type expr: Variable: 21753
                                                                └──Desc: Variable
                                                                   └──Variable: ctx
                                                       └──Expression:
                                                          └──Type expr: Constructor: var
                                                             └──Type expr: Variable: 21749
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
                   └──Constructor alphas: 21803
                   └──Constructor type:
                      └──Type expr: Constructor: value
                         └──Type expr: Variable: 21803
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: string
                   └──Constraint:
                      └──Type expr: Variable: 21803
                      └──Type expr: Constructor: string
                └──Constructor declaration:
                   └──Constructor name: Float
                   └──Constructor alphas: 21803
                   └──Constructor type:
                      └──Type expr: Constructor: value
                         └──Type expr: Variable: 21803
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: float
                   └──Constraint:
                      └──Type expr: Variable: 21803
                      └──Type expr: Constructor: float
                └──Constructor declaration:
                   └──Constructor name: Any
                   └──Constructor alphas: 21803
                   └──Constructor type:
                      └──Type expr: Constructor: value
                         └──Type expr: Variable: 21803
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
                   └──Constructor alphas: 21845 21846
                   └──Constructor type:
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: 21845
                         └──Type expr: Variable: 21846
                   └──Constraint:
                      └──Type expr: Variable: 21845
                      └──Type expr: Variable: 21846
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: eq
                         └──Type expr: Variable: 21865
                         └──Type expr: Tuple
                            └──Type expr: Variable: 21865
                            └──Type expr: Variable: 21865
                      └──Type expr: Constructor: unit
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: 21865
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: eq
                            └──Type expr: Variable: 21865
                            └──Type expr: Tuple
                               └──Type expr: Variable: 21865
                               └──Type expr: Variable: 21865
                         └──Type expr: Constructor: unit
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: eq
                               └──Type expr: Variable: 21865
                               └──Type expr: Tuple
                                  └──Type expr: Variable: 21865
                                  └──Type expr: Variable: 21865
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: unit
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: eq
                                     └──Type expr: Variable: 21865
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: 21865
                                        └──Type expr: Variable: 21865
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: eq
                                  └──Type expr: Variable: 21865
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: 21865
                                     └──Type expr: Variable: 21865
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: eq
                                           └──Type expr: Variable: 21865
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 21865
                                              └──Type expr: Variable: 21865
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Refl
                                              └──Constructor type:
                                                 └──Type expr: Constructor: eq
                                                    └──Type expr: Variable: 21865
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 21865
                                                       └──Type expr: Variable: 21865
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
                   └──Constructor alphas: 21880
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 21880
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: int
                   └──Constraint:
                      └──Type expr: Variable: 21880
                      └──Type expr: Constructor: int
                └──Constructor declaration:
                   └──Constructor name: Bool
                   └──Constructor alphas: 21880
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 21880
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: bool
                   └──Constraint:
                      └──Type expr: Variable: 21880
                      └──Type expr: Constructor: bool
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 21896
                      └──Type expr: Variable: 21896
                   └──Desc: Variable: check
                └──Abstraction:
                   └──Variables: 21896
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: 21896
                         └──Type expr: Variable: 21896
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: 21896
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Variable: 21896
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: 21896
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: 21896
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: 21896
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Int
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: int
                                              └──Constructor type:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: 21896
                                           └──Pattern:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable: n
                                     └──Expression:
                                        └──Type expr: Variable: 21896
                                        └──Desc: Variable
                                           └──Variable: n
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: 21896
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Bool
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: bool
                                              └──Constructor type:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: 21896
                                           └──Pattern:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Variable: b
                                     └──Expression:
                                        └──Type expr: Variable: 21896
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
  [%expect {|
    ("Type escape it's equational scope"
     ("Type_expr.decode type_expr" (Type 21946 (Var 21946)))) |}]

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
    ("Cannot unify types"
     ("Type_expr.decode type_expr1" (Type 21980 (Former (Constr () b))))
     ("Type_expr.decode type_expr2" (Type 21976 (Former (Constr () a))))) |}]

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
     ("Type_expr.decode type_expr1"
      (Type 22004 (Former (Constr ((Type 22003 (Var 22003))) t))))
     ("Type_expr.decode type_expr2" (Type 22002 (Former (Constr () int))))) |}]

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
                   └──Constructor alphas: 22006
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 22006
                   └──Constraint:
                      └──Type expr: Variable: 22006
                      └──Type expr: Constructor: int
       └──Structure item: Primitive
          └──Value description:
             └──Name: ignore
             └──Scheme:
                └──Variables: 22009
                └──Type expr: Arrow
                   └──Type expr: Variable: 22009
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
                         └──Type expr: Variable: 22056
                      └──Type expr: Variable: 22056
                   └──Desc: Variable: test
                └──Abstraction:
                   └──Variables: 22056
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: 22056
                         └──Type expr: Variable: 22056
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: 22056
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Variable: 22056
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: 22056
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: 22056
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: 22056
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Int
                                              └──Constructor type:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: 22056
                                     └──Expression:
                                        └──Type expr: Variable: 22056
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Variable: 22056
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 22056
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: int
                                                          └──Type expr: Variable: 22056
                                                    └──Desc: Variable
                                                       └──Variable: ky
                                                 └──Expression:
                                                    └──Type expr: Variable: 22056
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
  [%expect {|
    ("Type escape it's equational scope"
     ("Type_expr.decode type_expr" (Type 22133 (Var 22133)))) |}]

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
  [%expect {|
    ("Type escape it's equational scope"
     ("Type_expr.decode type_expr" (Type 22221 (Var 22221)))) |}]

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
    ("Cannot unify types"
     ("Type_expr.decode type_expr1" (Type 22328 (Var 22328)))
     ("Type_expr.decode type_expr2" (Type 22301 (Former (Constr () int))))) |}]

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
                   └──Constructor alphas: 22329
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 22329
                   └──Constraint:
                      └──Type expr: Variable: 22329
                      └──Type expr: Constructor: int
       └──Structure item: Primitive
          └──Value description:
             └──Name: ignore
             └──Scheme:
                └──Variables: 22332
                └──Type expr: Arrow
                   └──Type expr: Variable: 22332
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
                         └──Type expr: Variable: 22383
                      └──Type expr: Constructor: int
                   └──Desc: Variable: test
                └──Abstraction:
                   └──Variables: 22383
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: 22383
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: 22383
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
                                                    └──Type expr: Variable: 22383
                                                 └──Desc: Variable
                                                    └──Variable: x
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: 22383
                                              └──Cases:
                                                 └──Case:
                                                    └──Pattern:
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: 22383
                                                       └──Desc: Construct
                                                          └──Constructor description:
                                                             └──Name: Int
                                                             └──Constructor type:
                                                                └──Type expr: Constructor: t
                                                                   └──Type expr: Variable: 22383
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
                   └──Constructor alphas: 22401
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 22401
                   └──Constraint:
                      └──Type expr: Variable: 22401
                      └──Type expr: Constructor: int
       └──Structure item: Primitive
          └──Value description:
             └──Name: ignore
             └──Scheme:
                └──Variables: 22404
                └──Type expr: Arrow
                   └──Type expr: Variable: 22404
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
                         └──Type expr: Variable: 22451
                      └──Type expr: Variable: 22451
                   └──Desc: Variable: test
                └──Abstraction:
                   └──Variables: 22451
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: 22451
                         └──Type expr: Variable: 22451
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: 22451
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: 22451
                            └──Desc: Let
                               └──Value bindings:
                                  └──Value binding:
                                     └──Pattern:
                                        └──Type expr: Variable: 22451
                                        └──Desc: Variable: r
                                     └──Abstraction:
                                        └──Variables:
                                        └──Expression:
                                           └──Type expr: Variable: 22451
                                           └──Desc: Match
                                              └──Expression:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: 22451
                                                 └──Desc: Variable
                                                    └──Variable: x
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: 22451
                                              └──Cases:
                                                 └──Case:
                                                    └──Pattern:
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: 22451
                                                       └──Desc: Construct
                                                          └──Constructor description:
                                                             └──Name: Int
                                                             └──Constructor type:
                                                                └──Type expr: Constructor: t
                                                                   └──Type expr: Variable: 22451
                                                    └──Expression:
                                                       └──Type expr: Variable: 22451
                                                       └──Desc: Constant: 1
                               └──Expression:
                                  └──Type expr: Variable: 22451
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
                   └──Constructor alphas: 22470
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 22470
                   └──Constraint:
                      └──Type expr: Variable: 22470
                      └──Type expr: Constructor: int
       └──Structure item: Primitive
          └──Value description:
             └──Name: ignore
             └──Scheme:
                └──Variables: 22476
                └──Type expr: Arrow
                   └──Type expr: Variable: 22476
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
                         └──Type expr: Variable: 22523
                      └──Type expr: Constructor: int
                   └──Desc: Variable: test
                └──Abstraction:
                   └──Variables: 22523
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: 22523
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: 22523
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
                                                    └──Type expr: Variable: 22523
                                                 └──Desc: Variable
                                                    └──Variable: x
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: 22523
                                              └──Cases:
                                                 └──Case:
                                                    └──Pattern:
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: 22523
                                                       └──Desc: Construct
                                                          └──Constructor description:
                                                             └──Name: Int
                                                             └──Constructor type:
                                                                └──Type expr: Constructor: t
                                                                   └──Type expr: Variable: 22523
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
                   └──Constructor alphas: 22473
                   └──Constructor type:
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: 22473
                └──Constructor declaration:
                   └──Constructor name: Some
                   └──Constructor alphas: 22473
                   └──Constructor type:
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: 22473
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Variable: 22473
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 22544
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: 22544
                   └──Desc: Variable: test2
                └──Abstraction:
                   └──Variables: 22544
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: 22544
                         └──Type expr: Constructor: option
                            └──Type expr: Variable: 22544
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: 22544
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: option
                               └──Type expr: Variable: 22544
                            └──Desc: Let
                               └──Value bindings:
                                  └──Value binding:
                                     └──Pattern:
                                        └──Type expr: Constructor: ref
                                           └──Type expr: Constructor: option
                                              └──Type expr: Variable: 22544
                                        └──Desc: Variable: r
                                     └──Abstraction:
                                        └──Variables:
                                        └──Expression:
                                           └──Type expr: Constructor: ref
                                              └──Type expr: Constructor: option
                                                 └──Type expr: Variable: 22544
                                           └──Desc: Application
                                              └──Expression:
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Variable: 22544
                                                    └──Type expr: Constructor: ref
                                                       └──Type expr: Constructor: option
                                                          └──Type expr: Variable: 22544
                                                 └──Desc: Primitive: ref
                                              └──Expression:
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Variable: 22544
                                                 └──Desc: Construct
                                                    └──Constructor description:
                                                       └──Name: None
                                                       └──Constructor type:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Variable: 22544
                               └──Expression:
                                  └──Type expr: Constructor: option
                                     └──Type expr: Variable: 22544
                                  └──Desc: Sequence
                                     └──Expression:
                                        └──Type expr: Constructor: unit
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: 22544
                                              └──Desc: Variable
                                                 └──Variable: x
                                           └──Type expr: Constructor: t
                                              └──Type expr: Variable: 22544
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: t
                                                       └──Type expr: Variable: 22544
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: t
                                                                └──Type expr: Variable: 22544
                                                 └──Expression:
                                                    └──Type expr: Constructor: unit
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: option
                                                                └──Type expr: Variable: 22544
                                                             └──Type expr: Constructor: unit
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: ref
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Variable: 22544
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: option
                                                                         └──Type expr: Variable: 22544
                                                                      └──Type expr: Constructor: unit
                                                                └──Desc: Primitive: (:=)
                                                             └──Expression:
                                                                └──Type expr: Constructor: ref
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Variable: 22544
                                                                └──Desc: Variable
                                                                   └──Variable: r
                                                       └──Expression:
                                                          └──Type expr: Constructor: option
                                                             └──Type expr: Variable: 22544
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Some
                                                                └──Constructor argument type:
                                                                   └──Type expr: Variable: 22544
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: option
                                                                      └──Type expr: Variable: 22544
                                                             └──Expression:
                                                                └──Type expr: Variable: 22544
                                                                └──Desc: Constant: 1
                                     └──Expression:
                                        └──Type expr: Constructor: option
                                           └──Type expr: Variable: 22544
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: ref
                                                    └──Type expr: Constructor: option
                                                       └──Type expr: Variable: 22544
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Variable: 22544
                                              └──Desc: Primitive: (!)
                                           └──Expression:
                                              └──Type expr: Constructor: ref
                                                 └──Type expr: Constructor: option
                                                    └──Type expr: Variable: 22544
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
                   └──Constructor alphas: 22605
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 22605
                   └──Constraint:
                      └──Type expr: Variable: 22605
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
                      └──Type expr: Variable: 22631
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: 22631
                         └──Type expr: Constructor: int
                   └──Desc: Variable: we_y1x
                └──Abstraction:
                   └──Variables: 22631
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 22631
                         └──Type expr: Arrow
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: 22631
                            └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 22631
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: 22631
                               └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: 22631
                                  └──Desc: Variable: v
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: 22631
                                        └──Desc: Variable
                                           └──Variable: v
                                     └──Type expr: Constructor: t
                                        └──Type expr: Variable: 22631
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: 22631
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Int
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: 22631
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
                                                                      └──Type expr: Variable: 22631
                                                                      └──Type expr: Constructor: int
                                                                   └──Desc: Application
                                                                      └──Expression:
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: int
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Variable: 22631
                                                                               └──Type expr: Constructor: int
                                                                         └──Desc: Variable
                                                                            └──Variable: either
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: int
                                                                         └──Desc: Constant: 1
                                                                └──Expression:
                                                                   └──Type expr: Variable: 22631
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
                         └──Type expr: Variable: 22676
                      └──Type expr: Arrow
                         └──Type expr: Variable: 22676
                         └──Type expr: Variable: 22676
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: 22676
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: 22676
                         └──Type expr: Arrow
                            └──Type expr: Variable: 22676
                            └──Type expr: Variable: 22676
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: 22676
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: 22676
                               └──Type expr: Variable: 22676
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: 22676
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Variable: 22676
                                  └──Desc: Let
                                     └──Value bindings:
                                        └──Value binding:
                                           └──Pattern:
                                              └──Type expr: Variable: 22676
                                              └──Desc: Variable: r
                                           └──Abstraction:
                                              └──Variables:
                                              └──Expression:
                                                 └──Type expr: Variable: 22676
                                                 └──Desc: Match
                                                    └──Expression:
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: 22676
                                                       └──Desc: Variable
                                                          └──Variable: x
                                                    └──Type expr: Constructor: t
                                                       └──Type expr: Variable: 22676
                                                    └──Cases:
                                                       └──Case:
                                                          └──Pattern:
                                                             └──Type expr: Constructor: t
                                                                └──Type expr: Variable: 22676
                                                             └──Desc: Construct
                                                                └──Constructor description:
                                                                   └──Name: Int
                                                                   └──Constructor type:
                                                                      └──Type expr: Constructor: t
                                                                         └──Type expr: Variable: 22676
                                                          └──Expression:
                                                             └──Type expr: Variable: 22676
                                                             └──Desc: Variable
                                                                └──Variable: y
                                     └──Expression:
                                        └──Type expr: Variable: 22676
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
                   └──Constructor alphas: 22695
                   └──Constructor type:
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 22695
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: int
                   └──Constraint:
                      └──Type expr: Variable: 22695
                      └──Type expr: Constructor: int
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 22708
                      └──Type expr: Variable: 22708
                   └──Desc: Variable: f
                └──Abstraction:
                   └──Variables: 22708
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: 22708
                         └──Type expr: Variable: 22708
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: t
                               └──Type expr: Variable: 22708
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: 22708
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: 22708
                                  └──Desc: Variable
                                     └──Variable: x
                               └──Type expr: Constructor: t
                                  └──Type expr: Variable: 22708
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: 22708
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Int
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: int
                                              └──Constructor type:
                                                 └──Type expr: Constructor: t
                                                    └──Type expr: Variable: 22708
                                           └──Pattern:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable: y
                                     └──Expression:
                                        └──Type expr: Variable: 22708
                                        └──Desc: Variable
                                           └──Variable: y
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: t
                         └──Type expr: Variable: 22763
                      └──Type expr: Variable: 22763
                   └──Desc: Variable: g
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: t
                            └──Type expr: Variable: 22763
                         └──Type expr: Variable: 22763
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
                                  └──Type expr: Variable: 22763
                               └──Type expr: Variable: 22763
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: t
                                     └──Type expr: Variable: 22742
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Variable: 22742
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: t
                                           └──Type expr: Variable: 22742
                                        └──Desc: Variable
                                           └──Variable: x
                                     └──Type expr: Constructor: t
                                        └──Type expr: Variable: 22742
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: t
                                                 └──Type expr: Variable: 22742
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Int
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: int
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: t
                                                          └──Type expr: Variable: 22742
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable: y
                                           └──Expression:
                                              └──Type expr: Variable: 22742
                                              └──Desc: Variable
                                                 └──Variable: y |}]