open! Import
open Util

let%expect_test "" =
  let str = 
    {|
      let rec power = fun x n -> 
        if n = 0 
          then 1
          else x * power x (n - 1)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: power
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
                                  └──Desc: Variable: n
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: If
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
                                                       └──Variable: n
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 0
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 1
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
                                                    └──Desc: Primitive: (*)
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: x
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
                                                             └──Variable: power
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: x
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
                                                                └──Desc: Primitive: (-)
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: n
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Constant: 1 |}]

let%expect_test "" =
  let str = 
    {|
      external mod : int -> int -> int = "%mod";;

      let even = fun n -> mod n 2 = 0;;

      let rec power = fun x n ->
        if n = 1 
          then x
          else if even n 
            then power (x * x)  (n / 2)
            else x * power (x * x) (n / 2)
      ;; 
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Primitive
          └──Value description:
             └──Name: mod
             └──Scheme:
                └──Variables:
                └──Type expr: Arrow
                   └──Type expr: Constructor: int
                   └──Type expr: Arrow
                      └──Type expr: Constructor: int
                      └──Type expr: Constructor: int
             └──Primitive name: %mod
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: int
                      └──Type expr: Constructor: bool
                   └──Desc: Variable: even
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: n
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
                                                       └──Variable: mod
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: n
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 2
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Constant: 0
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: power
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
                                  └──Desc: Variable: n
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: If
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
                                                       └──Variable: n
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 1
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Variable
                                           └──Variable: x
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: If
                                           └──Expression:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Constructor: bool
                                                    └──Desc: Variable
                                                       └──Variable: even
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: n
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
                                                             └──Variable: power
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
                                                                      └──Desc: Primitive: (*)
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: x
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
                                                                └──Desc: Primitive: (/)
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: n
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Constant: 2
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
                                                          └──Desc: Primitive: (*)
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: x
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
                                                                   └──Variable: power
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
                                                                            └──Desc: Primitive: (*)
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: int
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Variable
                                                                         └──Variable: x
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
                                                                      └──Desc: Primitive: (/)
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Variable
                                                                         └──Variable: n
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Constant: 2 |}]

let%expect_test "" =
  let str = 
    {|
      let rec sum = 
        fun n -> 
          if n = 0 then 0 
          else n + sum (n - 1)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: sum
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: n
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: If
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
                                                 └──Variable: n
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 0
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Constant: 0
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
                                              └──Desc: Variable
                                                 └──Variable: n
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: sum
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
                                                          └──Desc: Primitive: (-)
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: n
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 1 |}]

let%expect_test "" =
  let str = 
    {|
      let rec sum = fun n ->
        let rec loop = fun n acc ->
          if n = 0 then acc
          else loop (n - 1) (n + acc)
        in sum n
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: sum
                └──Abstraction:
                   └──Variables: a22192,a22264
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a22264
                         └──Type expr: Variable: a22192
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a22264
                            └──Desc: Variable: n
                         └──Expression:
                            └──Type expr: Variable: a22192
                            └──Desc: Let rec
                               └──Value bindings:
                                  └──Value binding:
                                     └──Variable: loop
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
                                                 └──Desc: Variable: n
                                              └──Expression:
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: int
                                                 └──Desc: Function
                                                    └──Pattern:
                                                       └──Type expr: Constructor: int
                                                       └──Desc: Variable: acc
                                                    └──Expression:
                                                       └──Type expr: Constructor: int
                                                       └──Desc: If
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
                                                                            └──Variable: n
                                                                └──Expression:
                                                                   └──Type expr: Constructor: int
                                                                   └──Desc: Constant: 0
                                                          └──Expression:
                                                             └──Type expr: Constructor: int
                                                             └──Desc: Variable
                                                                └──Variable: acc
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
                                                                            └──Variable: loop
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
                                                                                     └──Desc: Primitive: (-)
                                                                                  └──Expression:
                                                                                     └──Type expr: Constructor: int
                                                                                     └──Desc: Variable
                                                                                        └──Variable: n
                                                                            └──Expression:
                                                                               └──Type expr: Constructor: int
                                                                               └──Desc: Constant: 1
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
                                                                               └──Desc: Variable
                                                                                  └──Variable: n
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: int
                                                                         └──Desc: Variable
                                                                            └──Variable: acc
                               └──Expression:
                                  └──Type expr: Variable: a22192
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: a22264
                                           └──Type expr: Variable: a22192
                                        └──Desc: Variable
                                           └──Variable: sum
                                     └──Expression:
                                        └──Type expr: Variable: a22264
                                        └──Desc: Variable
                                           └──Variable: n |}]

let%expect_test "" =
  let str = 
    {|
      type 'a list =
        | Nil
        | Cons of 'a * 'a list
      ;;

      let rec mem = fun t x equal ->
        match t with
        ( Nil -> false
        | Cons (y, t) -> 
          if equal x y then true 
          else mem t x equal 
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
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: a
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: mem
                └──Abstraction:
                   └──Variables: a22310,a22299
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a22299
                         └──Type expr: Arrow
                            └──Type expr: Variable: a22310
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a22310
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a22299
                                     └──Type expr: Constructor: bool
                               └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a22299
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a22310
                               └──Type expr: Arrow
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a22310
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: a22299
                                        └──Type expr: Constructor: bool
                                  └──Type expr: Constructor: bool
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: a22310
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: a22310
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: a22299
                                           └──Type expr: Constructor: bool
                                     └──Type expr: Constructor: bool
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: a22310
                                           └──Type expr: Arrow
                                              └──Type expr: Variable: a22299
                                              └──Type expr: Constructor: bool
                                        └──Desc: Variable: equal
                                     └──Expression:
                                        └──Type expr: Constructor: bool
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a22299
                                              └──Desc: Variable
                                                 └──Variable: t
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a22299
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a22299
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Nil
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a22299
                                                 └──Expression:
                                                    └──Type expr: Constructor: bool
                                                    └──Desc: Constant: false
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a22299
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Cons
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a22299
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a22299
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a22299
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a22299
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a22299
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Variable: a22299
                                                                └──Desc: Variable: y
                                                             └──Pattern:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a22299
                                                                └──Desc: Variable: t
                                                 └──Expression:
                                                    └──Type expr: Constructor: bool
                                                    └──Desc: If
                                                       └──Expression:
                                                          └──Type expr: Constructor: bool
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: a22299
                                                                   └──Type expr: Constructor: bool
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: a22310
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Variable: a22299
                                                                            └──Type expr: Constructor: bool
                                                                      └──Desc: Variable
                                                                         └──Variable: equal
                                                                   └──Expression:
                                                                      └──Type expr: Variable: a22310
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                                             └──Expression:
                                                                └──Type expr: Variable: a22299
                                                                └──Desc: Variable
                                                                   └──Variable: y
                                                       └──Expression:
                                                          └──Type expr: Constructor: bool
                                                          └──Desc: Constant: true
                                                       └──Expression:
                                                          └──Type expr: Constructor: bool
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a22310
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: a22299
                                                                         └──Type expr: Constructor: bool
                                                                   └──Type expr: Constructor: bool
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: a22310
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Variable: a22310
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: a22299
                                                                                  └──Type expr: Constructor: bool
                                                                            └──Type expr: Constructor: bool
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Variable: a22299
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: a22310
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Variable: a22310
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Variable: a22299
                                                                                           └──Type expr: Constructor: bool
                                                                                     └──Type expr: Constructor: bool
                                                                            └──Desc: Variable
                                                                               └──Variable: mem
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: a22299
                                                                            └──Desc: Variable
                                                                               └──Variable: t
                                                                   └──Expression:
                                                                      └──Type expr: Variable: a22310
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: a22310
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a22299
                                                                      └──Type expr: Constructor: bool
                                                                └──Desc: Variable
                                                                   └──Variable: equal |}]

let%expect_test "" =
  let str = 
    {|
      type 'a list =
        | Nil
        | Cons of 'a * 'a list
      ;;

      let rec zip = 
        fun t1 t2 ->
          match (t1, t2) with
          ( (Cons (x1, t1), Cons (x2, t2) ->
              Cons ((x1, x2), zip t1 t2) 
          | _ -> Nil  
          )
      ;;
    |}
  in
  print_infer_result str;
  [%expect {| "parse error" |}]

let%expect_test "" =
  let str = 
    {|
      type 'a list =
        | Nil
        | Cons of 'a * 'a list
      ;;

      let rec unzip = 
        fun t ->
          match t with
          ( Nil -> (Nil, Nil)
          | Cons ((x1, x2), t) ->
            let (t1, t2) = unzip t in
            (Cons (x1, t1), Cons (x2, t2))    
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
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: a
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: unzip
                └──Abstraction:
                   └──Variables: a22375,a22364
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: list
                            └──Type expr: Tuple
                               └──Type expr: Variable: a22364
                               └──Type expr: Variable: a22375
                         └──Type expr: Tuple
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a22364
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a22375
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: list
                               └──Type expr: Tuple
                                  └──Type expr: Variable: a22364
                                  └──Type expr: Variable: a22375
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Tuple
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a22364
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a22375
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a22364
                                        └──Type expr: Variable: a22375
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: list
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: a22364
                                     └──Type expr: Variable: a22375
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a22364
                                              └──Type expr: Variable: a22375
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Nil
                                              └──Constructor type:
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a22364
                                                       └──Type expr: Variable: a22375
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a22364
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a22375
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a22364
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a22364
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a22375
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a22375
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a22364
                                              └──Type expr: Variable: a22375
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Cons
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a22364
                                                       └──Type expr: Variable: a22375
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a22364
                                                          └──Type expr: Variable: a22375
                                              └──Constructor type:
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a22364
                                                       └──Type expr: Variable: a22375
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a22364
                                                    └──Type expr: Variable: a22375
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a22364
                                                       └──Type expr: Variable: a22375
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a22364
                                                       └──Type expr: Variable: a22375
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Variable: a22364
                                                          └──Desc: Variable: x1
                                                       └──Pattern:
                                                          └──Type expr: Variable: a22375
                                                          └──Desc: Variable: x2
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a22364
                                                          └──Type expr: Variable: a22375
                                                    └──Desc: Variable: t
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a22364
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a22375
                                        └──Desc: Let
                                           └──Value bindings:
                                              └──Value binding:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a22364
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a22375
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a22364
                                                          └──Desc: Variable: t1
                                                       └──Pattern:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a22375
                                                          └──Desc: Variable: t2
                                                 └──Abstraction:
                                                    └──Variables:
                                                    └──Expression:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a22364
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a22375
                                                       └──Desc: Application
                                                          └──Expression:
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a22364
                                                                      └──Type expr: Variable: a22375
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: a22364
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: a22375
                                                             └──Desc: Variable
                                                                └──Variable: unzip
                                                          └──Expression:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a22364
                                                                   └──Type expr: Variable: a22375
                                                             └──Desc: Variable
                                                                └──Variable: t
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: a22364
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: a22375
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a22364
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Cons
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a22364
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a22364
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a22364
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a22364
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a22364
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Variable: a22364
                                                                └──Desc: Variable
                                                                   └──Variable: x1
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a22364
                                                                └──Desc: Variable
                                                                   └──Variable: t1
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a22375
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Cons
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a22375
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a22375
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a22375
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a22375
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a22375
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Variable: a22375
                                                                └──Desc: Variable
                                                                   └──Variable: x2
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a22375
                                                                └──Desc: Variable
                                                                   └──Variable: t2 |}]

let%expect_test "" =
  let str = 
    {|
      type 'a list =
        | Nil
        | Cons of 'a * 'a list
      ;;

      external raise : 'a. exn -> 'a = "%raise";;

      exception Failure of string;;

      external lt : 'a. 'a -> 'a -> bool = "%less_than";;
      
      let rec change = 
        fun till amt ->
          match (till, amt) with
          ( (_, 0) -> Nil
          | (Nil, _) -> raise (Failure "no more coins!")
          | (Cons (c, till), amt) ->
            if lt amt c then change till amt
            else Cons (c, change (Cons (c, till)) (amt - c) )     
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
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: a
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a
       └──Structure item: Primitive
          └──Value description:
             └──Name: raise
             └──Scheme:
                └──Variables: a22386
                └──Type expr: Arrow
                   └──Type expr: Constructor: exn
                   └──Type expr: Variable: a22386
             └──Primitive name: %raise
       └──Structure item: Exception
          └──Type exception:
             └──Extension constructor:
                └──Extension name: exn
                └──Extension parameters:
                └──Extension constructor kind: Declaration
                   └──Constructor declaration:
                      └──Constructor name: Failure
                      └──Constructor alphas:
                      └──Constructor type:
                         └──Type expr: Constructor: exn
                      └──Constructor argument:
                         └──Constructor betas:
                         └──Type expr: Constructor: string
       └──Structure item: Primitive
          └──Value description:
             └──Name: lt
             └──Scheme:
                └──Variables: a22391
                └──Type expr: Arrow
                   └──Type expr: Variable: a22391
                   └──Type expr: Arrow
                      └──Type expr: Variable: a22391
                      └──Type expr: Constructor: bool
             └──Primitive name: %less_than
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: change
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: list
                            └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Constructor: int
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: int
                            └──Desc: Variable: till
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Constructor: list
                                  └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable: amt
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Constructor: int
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: list
                                              └──Type expr: Constructor: int
                                           └──Type expr: Constructor: int
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: till
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: amt
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: list
                                           └──Type expr: Constructor: int
                                        └──Type expr: Constructor: int
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Any
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 0
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: int
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: int
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Nil
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Any
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: int
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: exn
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: raise
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: int
                                                 └──Expression:
                                                    └──Type expr: Constructor: exn
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Failure
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: string
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: exn
                                                       └──Expression:
                                                          └──Type expr: Constructor: string
                                                          └──Desc: Constant: no more coins!
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Cons
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable: c
                                                             └──Pattern:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: int
                                                                └──Desc: Variable: till
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable: amt
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: int
                                              └──Desc: If
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
                                                                └──Desc: Variable
                                                                   └──Variable: lt
                                                                   └──Type expr: Constructor: int
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: amt
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: c
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: int
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: int
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: change
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: till
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: amt
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Cons
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: c
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: int
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: int
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: int
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: int
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: int
                                                                                  └──Type expr: Constructor: list
                                                                                     └──Type expr: Constructor: int
                                                                            └──Desc: Variable
                                                                               └──Variable: change
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: int
                                                                            └──Desc: Construct
                                                                               └──Constructor description:
                                                                                  └──Name: Cons
                                                                                  └──Constructor argument type:
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Constructor: int
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Constructor: int
                                                                                  └──Constructor type:
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Constructor: int
                                                                               └──Expression:
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Constructor: int
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Constructor: int
                                                                                  └──Desc: Tuple
                                                                                     └──Expression:
                                                                                        └──Type expr: Constructor: int
                                                                                        └──Desc: Variable
                                                                                           └──Variable: c
                                                                                     └──Expression:
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Constructor: int
                                                                                        └──Desc: Variable
                                                                                           └──Variable: till
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
                                                                                  └──Desc: Primitive: (-)
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: int
                                                                                  └──Desc: Variable
                                                                                     └──Variable: amt
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: int
                                                                            └──Desc: Variable
                                                                               └──Variable: c |}]

let%expect_test "" =
  let str = 
    {|
      type 'a list =
        | Nil
        | Cons of 'a * 'a list
      ;;

      external append : 'a. 'a list -> 'a list -> 'a list = "%append";;

      external lt : 'a. 'a -> 'a -> bool = "%less_than";;

      let rec change = 
        fun till amt ->
          match (till, amt) with
          ( (_, 0) -> Cons (Nil, Nil)
          | (Nil, _) -> Nil
          | (Cons (c, till), amt) ->
            if lt amt c then change till amt
            else 
              let rec loop = fun t -> 
                match t with
                ( Nil -> Nil
                | Cons (cs, css) -> Cons (Cons (c, cs), loop css)
                )
              in
                append 
                  (loop (change (Cons (c, till)) (amt - c)))
                  (change till amt)  
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
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: a
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a
       └──Structure item: Primitive
          └──Value description:
             └──Name: append
             └──Scheme:
                └──Variables: a22519
                └──Type expr: Arrow
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: a22519
                   └──Type expr: Arrow
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a22519
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a22519
             └──Primitive name: %append
       └──Structure item: Primitive
          └──Value description:
             └──Name: lt
             └──Scheme:
                └──Variables: a22530
                └──Type expr: Arrow
                   └──Type expr: Variable: a22530
                   └──Type expr: Arrow
                      └──Type expr: Variable: a22530
                      └──Type expr: Constructor: bool
             └──Primitive name: %less_than
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: change
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: list
                            └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Constructor: int
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: list
                                  └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: int
                            └──Desc: Variable: till
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Constructor: list
                                  └──Type expr: Constructor: list
                                     └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable: amt
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Constructor: list
                                        └──Type expr: Constructor: int
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: list
                                              └──Type expr: Constructor: int
                                           └──Type expr: Constructor: int
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: till
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: amt
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: list
                                           └──Type expr: Constructor: int
                                        └──Type expr: Constructor: int
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Any
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 0
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: int
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: int
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: int
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: int
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Nil
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: int
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Nil
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: int
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Nil
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Any
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: int
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: int
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Cons
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable: c
                                                             └──Pattern:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: int
                                                                └──Desc: Variable: till
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable: amt
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: int
                                              └──Desc: If
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
                                                                └──Desc: Variable
                                                                   └──Variable: lt
                                                                   └──Type expr: Constructor: int
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: amt
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: c
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: int
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: int
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: int
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: int
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: change
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: till
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: amt
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: int
                                                    └──Desc: Let rec
                                                       └──Value bindings:
                                                          └──Value binding:
                                                             └──Variable: loop
                                                             └──Abstraction:
                                                                └──Variables:
                                                                └──Expression:
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: int
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: int
                                                                   └──Desc: Function
                                                                      └──Pattern:
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: int
                                                                         └──Desc: Variable: t
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: int
                                                                         └──Desc: Match
                                                                            └──Expression:
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: list
                                                                                     └──Type expr: Constructor: int
                                                                               └──Desc: Variable
                                                                                  └──Variable: t
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: int
                                                                            └──Cases:
                                                                               └──Case:
                                                                                  └──Pattern:
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Constructor: int
                                                                                     └──Desc: Construct
                                                                                        └──Constructor description:
                                                                                           └──Name: Nil
                                                                                           └──Constructor type:
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: int
                                                                                  └──Expression:
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Constructor: int
                                                                                     └──Desc: Construct
                                                                                        └──Constructor description:
                                                                                           └──Name: Nil
                                                                                           └──Constructor type:
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: int
                                                                               └──Case:
                                                                                  └──Pattern:
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Constructor: int
                                                                                     └──Desc: Construct
                                                                                        └──Constructor description:
                                                                                           └──Name: Cons
                                                                                           └──Constructor argument type:
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: int
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: list
                                                                                                       └──Type expr: Constructor: int
                                                                                           └──Constructor type:
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: int
                                                                                        └──Pattern:
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Constructor: int
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: int
                                                                                           └──Desc: Tuple
                                                                                              └──Pattern:
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: int
                                                                                                 └──Desc: Variable: cs
                                                                                              └──Pattern:
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: list
                                                                                                       └──Type expr: Constructor: int
                                                                                                 └──Desc: Variable: css
                                                                                  └──Expression:
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Constructor: int
                                                                                     └──Desc: Construct
                                                                                        └──Constructor description:
                                                                                           └──Name: Cons
                                                                                           └──Constructor argument type:
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: int
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: list
                                                                                                       └──Type expr: Constructor: int
                                                                                           └──Constructor type:
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: int
                                                                                        └──Expression:
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Constructor: int
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: int
                                                                                           └──Desc: Tuple
                                                                                              └──Expression:
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: int
                                                                                                 └──Desc: Construct
                                                                                                    └──Constructor description:
                                                                                                       └──Name: Cons
                                                                                                       └──Constructor argument type:
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Constructor: int
                                                                                                             └──Type expr: Constructor: list
                                                                                                                └──Type expr: Constructor: int
                                                                                                       └──Constructor type:
                                                                                                          └──Type expr: Constructor: list
                                                                                                             └──Type expr: Constructor: int
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Constructor: int
                                                                                                          └──Type expr: Constructor: list
                                                                                                             └──Type expr: Constructor: int
                                                                                                       └──Desc: Tuple
                                                                                                          └──Expression:
                                                                                                             └──Type expr: Constructor: int
                                                                                                             └──Desc: Variable
                                                                                                                └──Variable: c
                                                                                                          └──Expression:
                                                                                                             └──Type expr: Constructor: list
                                                                                                                └──Type expr: Constructor: int
                                                                                                             └──Desc: Variable
                                                                                                                └──Variable: cs
                                                                                              └──Expression:
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: list
                                                                                                       └──Type expr: Constructor: int
                                                                                                 └──Desc: Application
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Constructor: list
                                                                                                             └──Type expr: Constructor: list
                                                                                                                └──Type expr: Constructor: int
                                                                                                          └──Type expr: Constructor: list
                                                                                                             └──Type expr: Constructor: list
                                                                                                                └──Type expr: Constructor: int
                                                                                                       └──Desc: Variable
                                                                                                          └──Variable: loop
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Constructor: list
                                                                                                          └──Type expr: Constructor: list
                                                                                                             └──Type expr: Constructor: int
                                                                                                       └──Desc: Variable
                                                                                                          └──Variable: css
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: int
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: int
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: int
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: int
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: int
                                                                      └──Desc: Variable
                                                                         └──Variable: append
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: int
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: int
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: list
                                                                                     └──Type expr: Constructor: int
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: list
                                                                                     └──Type expr: Constructor: int
                                                                            └──Desc: Variable
                                                                               └──Variable: loop
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: int
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: int
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Constructor: int
                                                                                  └──Desc: Application
                                                                                     └──Expression:
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Constructor: list
                                                                                              └──Type expr: Constructor: int
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Constructor: int
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: int
                                                                                        └──Desc: Variable
                                                                                           └──Variable: change
                                                                                     └──Expression:
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Constructor: int
                                                                                        └──Desc: Construct
                                                                                           └──Constructor description:
                                                                                              └──Name: Cons
                                                                                              └──Constructor argument type:
                                                                                                 └──Type expr: Tuple
                                                                                                    └──Type expr: Constructor: int
                                                                                                    └──Type expr: Constructor: list
                                                                                                       └──Type expr: Constructor: int
                                                                                              └──Constructor type:
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: int
                                                                                           └──Expression:
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Constructor: int
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: int
                                                                                              └──Desc: Tuple
                                                                                                 └──Expression:
                                                                                                    └──Type expr: Constructor: int
                                                                                                    └──Desc: Variable
                                                                                                       └──Variable: c
                                                                                                 └──Expression:
                                                                                                    └──Type expr: Constructor: list
                                                                                                       └──Type expr: Constructor: int
                                                                                                    └──Desc: Variable
                                                                                                       └──Variable: till
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
                                                                                              └──Desc: Primitive: (-)
                                                                                           └──Expression:
                                                                                              └──Type expr: Constructor: int
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: amt
                                                                                     └──Expression:
                                                                                        └──Type expr: Constructor: int
                                                                                        └──Desc: Variable
                                                                                           └──Variable: c
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: int
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: int
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: int
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: int
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: int
                                                                                  └──Type expr: Constructor: list
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Constructor: int
                                                                            └──Desc: Variable
                                                                               └──Variable: change
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: int
                                                                            └──Desc: Variable
                                                                               └──Variable: till
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Variable
                                                                         └──Variable: amt |}]

let%expect_test "" =
  let str = 
    {|
      type 'a list =
        | Nil
        | Cons of 'a * 'a list
      ;;

      external lt : 'a. 'a -> 'a -> bool = "%less_than";;

      let rec change = 
        fun till amt ->
          let rec loop = fun till amt chg chgs ->
            match (till, amt) with
            ( (_, 0) -> Cons (chg, chgs)
            | (Nil, _) -> chgs
            | (Cons (c, till), amt) ->
                if lt amt 0 then chgs
                else
                  loop (Cons (c, till)) (amt - c) (Cons (c, chg)) (loop till amt chg chgs) 
            )
          in loop till amt Nil Nil
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
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
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: a
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a
       └──Structure item: Primitive
          └──Value description:
             └──Name: lt
             └──Scheme:
                └──Variables: a22728
                └──Type expr: Arrow
                   └──Type expr: Variable: a22728
                   └──Type expr: Arrow
                      └──Type expr: Variable: a22728
                      └──Type expr: Constructor: bool
             └──Primitive name: %less_than
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: change
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: list
                            └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Constructor: int
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: list
                                  └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: int
                            └──Desc: Variable: till
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Constructor: list
                                  └──Type expr: Constructor: list
                                     └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable: amt
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Constructor: list
                                        └──Type expr: Constructor: int
                                  └──Desc: Let rec
                                     └──Value bindings:
                                        └──Value binding:
                                           └──Variable: loop
                                           └──Abstraction:
                                              └──Variables:
                                              └──Expression:
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: int
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: int
                                                 └──Desc: Function
                                                    └──Pattern:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: int
                                                       └──Desc: Variable: till
                                                    └──Expression:
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: int
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: int
                                                       └──Desc: Function
                                                          └──Pattern:
                                                             └──Type expr: Constructor: int
                                                             └──Desc: Variable: amt
                                                          └──Expression:
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: int
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: int
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: int
                                                             └──Desc: Function
                                                                └──Pattern:
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: int
                                                                   └──Desc: Variable: chg
                                                                └──Expression:
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: int
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: int
                                                                   └──Desc: Function
                                                                      └──Pattern:
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: int
                                                                         └──Desc: Variable: chgs
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: int
                                                                         └──Desc: Match
                                                                            └──Expression:
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Constructor: list
                                                                                     └──Type expr: Constructor: int
                                                                                  └──Type expr: Constructor: int
                                                                               └──Desc: Tuple
                                                                                  └──Expression:
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Constructor: int
                                                                                     └──Desc: Variable
                                                                                        └──Variable: till
                                                                                  └──Expression:
                                                                                     └──Type expr: Constructor: int
                                                                                     └──Desc: Variable
                                                                                        └──Variable: amt
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: int
                                                                               └──Type expr: Constructor: int
                                                                            └──Cases:
                                                                               └──Case:
                                                                                  └──Pattern:
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Constructor: int
                                                                                        └──Type expr: Constructor: int
                                                                                     └──Desc: Tuple
                                                                                        └──Pattern:
                                                                                           └──Type expr: Constructor: list
                                                                                              └──Type expr: Constructor: int
                                                                                           └──Desc: Any
                                                                                        └──Pattern:
                                                                                           └──Type expr: Constructor: int
                                                                                           └──Desc: Constant: 0
                                                                                  └──Expression:
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Constructor: int
                                                                                     └──Desc: Construct
                                                                                        └──Constructor description:
                                                                                           └──Name: Cons
                                                                                           └──Constructor argument type:
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: int
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: list
                                                                                                       └──Type expr: Constructor: int
                                                                                           └──Constructor type:
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: int
                                                                                        └──Expression:
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Constructor: int
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: int
                                                                                           └──Desc: Tuple
                                                                                              └──Expression:
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: int
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: chg
                                                                                              └──Expression:
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: list
                                                                                                       └──Type expr: Constructor: int
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: chgs
                                                                               └──Case:
                                                                                  └──Pattern:
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Constructor: int
                                                                                        └──Type expr: Constructor: int
                                                                                     └──Desc: Tuple
                                                                                        └──Pattern:
                                                                                           └──Type expr: Constructor: list
                                                                                              └──Type expr: Constructor: int
                                                                                           └──Desc: Construct
                                                                                              └──Constructor description:
                                                                                                 └──Name: Nil
                                                                                                 └──Constructor type:
                                                                                                    └──Type expr: Constructor: list
                                                                                                       └──Type expr: Constructor: int
                                                                                        └──Pattern:
                                                                                           └──Type expr: Constructor: int
                                                                                           └──Desc: Any
                                                                                  └──Expression:
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Constructor: int
                                                                                     └──Desc: Variable
                                                                                        └──Variable: chgs
                                                                               └──Case:
                                                                                  └──Pattern:
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Constructor: int
                                                                                        └──Type expr: Constructor: int
                                                                                     └──Desc: Tuple
                                                                                        └──Pattern:
                                                                                           └──Type expr: Constructor: list
                                                                                              └──Type expr: Constructor: int
                                                                                           └──Desc: Construct
                                                                                              └──Constructor description:
                                                                                                 └──Name: Cons
                                                                                                 └──Constructor argument type:
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Constructor: int
                                                                                                       └──Type expr: Constructor: list
                                                                                                          └──Type expr: Constructor: int
                                                                                                 └──Constructor type:
                                                                                                    └──Type expr: Constructor: list
                                                                                                       └──Type expr: Constructor: int
                                                                                              └──Pattern:
                                                                                                 └──Type expr: Tuple
                                                                                                    └──Type expr: Constructor: int
                                                                                                    └──Type expr: Constructor: list
                                                                                                       └──Type expr: Constructor: int
                                                                                                 └──Desc: Tuple
                                                                                                    └──Pattern:
                                                                                                       └──Type expr: Constructor: int
                                                                                                       └──Desc: Variable: c
                                                                                                    └──Pattern:
                                                                                                       └──Type expr: Constructor: list
                                                                                                          └──Type expr: Constructor: int
                                                                                                       └──Desc: Variable: till
                                                                                        └──Pattern:
                                                                                           └──Type expr: Constructor: int
                                                                                           └──Desc: Variable: amt
                                                                                  └──Expression:
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Constructor: int
                                                                                     └──Desc: If
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
                                                                                                       └──Desc: Variable
                                                                                                          └──Variable: lt
                                                                                                          └──Type expr: Constructor: int
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Constructor: int
                                                                                                       └──Desc: Variable
                                                                                                          └──Variable: amt
                                                                                              └──Expression:
                                                                                                 └──Type expr: Constructor: int
                                                                                                 └──Desc: Constant: 0
                                                                                        └──Expression:
                                                                                           └──Type expr: Constructor: list
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Constructor: int
                                                                                           └──Desc: Variable
                                                                                              └──Variable: chgs
                                                                                        └──Expression:
                                                                                           └──Type expr: Constructor: list
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Constructor: int
                                                                                           └──Desc: Application
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Constructor: list
                                                                                                       └──Type expr: Constructor: list
                                                                                                          └──Type expr: Constructor: int
                                                                                                    └──Type expr: Constructor: list
                                                                                                       └──Type expr: Constructor: list
                                                                                                          └──Type expr: Constructor: int
                                                                                                 └──Desc: Application
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Constructor: list
                                                                                                             └──Type expr: Constructor: int
                                                                                                          └──Type expr: Arrow
                                                                                                             └──Type expr: Constructor: list
                                                                                                                └──Type expr: Constructor: list
                                                                                                                   └──Type expr: Constructor: int
                                                                                                             └──Type expr: Constructor: list
                                                                                                                └──Type expr: Constructor: list
                                                                                                                   └──Type expr: Constructor: int
                                                                                                       └──Desc: Application
                                                                                                          └──Expression:
                                                                                                             └──Type expr: Arrow
                                                                                                                └──Type expr: Constructor: int
                                                                                                                └──Type expr: Arrow
                                                                                                                   └──Type expr: Constructor: list
                                                                                                                      └──Type expr: Constructor: int
                                                                                                                   └──Type expr: Arrow
                                                                                                                      └──Type expr: Constructor: list
                                                                                                                         └──Type expr: Constructor: list
                                                                                                                            └──Type expr: Constructor: int
                                                                                                                      └──Type expr: Constructor: list
                                                                                                                         └──Type expr: Constructor: list
                                                                                                                            └──Type expr: Constructor: int
                                                                                                             └──Desc: Application
                                                                                                                └──Expression:
                                                                                                                   └──Type expr: Arrow
                                                                                                                      └──Type expr: Constructor: list
                                                                                                                         └──Type expr: Constructor: int
                                                                                                                      └──Type expr: Arrow
                                                                                                                         └──Type expr: Constructor: int
                                                                                                                         └──Type expr: Arrow
                                                                                                                            └──Type expr: Constructor: list
                                                                                                                               └──Type expr: Constructor: int
                                                                                                                            └──Type expr: Arrow
                                                                                                                               └──Type expr: Constructor: list
                                                                                                                                  └──Type expr: Constructor: list
                                                                                                                                     └──Type expr: Constructor: int
                                                                                                                               └──Type expr: Constructor: list
                                                                                                                                  └──Type expr: Constructor: list
                                                                                                                                     └──Type expr: Constructor: int
                                                                                                                   └──Desc: Variable
                                                                                                                      └──Variable: loop
                                                                                                                └──Expression:
                                                                                                                   └──Type expr: Constructor: list
                                                                                                                      └──Type expr: Constructor: int
                                                                                                                   └──Desc: Construct
                                                                                                                      └──Constructor description:
                                                                                                                         └──Name: Cons
                                                                                                                         └──Constructor argument type:
                                                                                                                            └──Type expr: Tuple
                                                                                                                               └──Type expr: Constructor: int
                                                                                                                               └──Type expr: Constructor: list
                                                                                                                                  └──Type expr: Constructor: int
                                                                                                                         └──Constructor type:
                                                                                                                            └──Type expr: Constructor: list
                                                                                                                               └──Type expr: Constructor: int
                                                                                                                      └──Expression:
                                                                                                                         └──Type expr: Tuple
                                                                                                                            └──Type expr: Constructor: int
                                                                                                                            └──Type expr: Constructor: list
                                                                                                                               └──Type expr: Constructor: int
                                                                                                                         └──Desc: Tuple
                                                                                                                            └──Expression:
                                                                                                                               └──Type expr: Constructor: int
                                                                                                                               └──Desc: Variable
                                                                                                                                  └──Variable: c
                                                                                                                            └──Expression:
                                                                                                                               └──Type expr: Constructor: list
                                                                                                                                  └──Type expr: Constructor: int
                                                                                                                               └──Desc: Variable
                                                                                                                                  └──Variable: till
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
                                                                                                                         └──Desc: Primitive: (-)
                                                                                                                      └──Expression:
                                                                                                                         └──Type expr: Constructor: int
                                                                                                                         └──Desc: Variable
                                                                                                                            └──Variable: amt
                                                                                                                └──Expression:
                                                                                                                   └──Type expr: Constructor: int
                                                                                                                   └──Desc: Variable
                                                                                                                      └──Variable: c
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Constructor: list
                                                                                                          └──Type expr: Constructor: int
                                                                                                       └──Desc: Construct
                                                                                                          └──Constructor description:
                                                                                                             └──Name: Cons
                                                                                                             └──Constructor argument type:
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Constructor: int
                                                                                                                   └──Type expr: Constructor: list
                                                                                                                      └──Type expr: Constructor: int
                                                                                                             └──Constructor type:
                                                                                                                └──Type expr: Constructor: list
                                                                                                                   └──Type expr: Constructor: int
                                                                                                          └──Expression:
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Constructor: int
                                                                                                                └──Type expr: Constructor: list
                                                                                                                   └──Type expr: Constructor: int
                                                                                                             └──Desc: Tuple
                                                                                                                └──Expression:
                                                                                                                   └──Type expr: Constructor: int
                                                                                                                   └──Desc: Variable
                                                                                                                      └──Variable: c
                                                                                                                └──Expression:
                                                                                                                   └──Type expr: Constructor: list
                                                                                                                      └──Type expr: Constructor: int
                                                                                                                   └──Desc: Variable
                                                                                                                      └──Variable: chg
                                                                                              └──Expression:
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: list
                                                                                                       └──Type expr: Constructor: int
                                                                                                 └──Desc: Application
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Constructor: list
                                                                                                             └──Type expr: Constructor: list
                                                                                                                └──Type expr: Constructor: int
                                                                                                          └──Type expr: Constructor: list
                                                                                                             └──Type expr: Constructor: list
                                                                                                                └──Type expr: Constructor: int
                                                                                                       └──Desc: Application
                                                                                                          └──Expression:
                                                                                                             └──Type expr: Arrow
                                                                                                                └──Type expr: Constructor: list
                                                                                                                   └──Type expr: Constructor: int
                                                                                                                └──Type expr: Arrow
                                                                                                                   └──Type expr: Constructor: list
                                                                                                                      └──Type expr: Constructor: list
                                                                                                                         └──Type expr: Constructor: int
                                                                                                                   └──Type expr: Constructor: list
                                                                                                                      └──Type expr: Constructor: list
                                                                                                                         └──Type expr: Constructor: int
                                                                                                             └──Desc: Application
                                                                                                                └──Expression:
                                                                                                                   └──Type expr: Arrow
                                                                                                                      └──Type expr: Constructor: int
                                                                                                                      └──Type expr: Arrow
                                                                                                                         └──Type expr: Constructor: list
                                                                                                                            └──Type expr: Constructor: int
                                                                                                                         └──Type expr: Arrow
                                                                                                                            └──Type expr: Constructor: list
                                                                                                                               └──Type expr: Constructor: list
                                                                                                                                  └──Type expr: Constructor: int
                                                                                                                            └──Type expr: Constructor: list
                                                                                                                               └──Type expr: Constructor: list
                                                                                                                                  └──Type expr: Constructor: int
                                                                                                                   └──Desc: Application
                                                                                                                      └──Expression:
                                                                                                                         └──Type expr: Arrow
                                                                                                                            └──Type expr: Constructor: list
                                                                                                                               └──Type expr: Constructor: int
                                                                                                                            └──Type expr: Arrow
                                                                                                                               └──Type expr: Constructor: int
                                                                                                                               └──Type expr: Arrow
                                                                                                                                  └──Type expr: Constructor: list
                                                                                                                                     └──Type expr: Constructor: int
                                                                                                                                  └──Type expr: Arrow
                                                                                                                                     └──Type expr: Constructor: list
                                                                                                                                        └──Type expr: Constructor: list
                                                                                                                                           └──Type expr: Constructor: int
                                                                                                                                     └──Type expr: Constructor: list
                                                                                                                                        └──Type expr: Constructor: list
                                                                                                                                           └──Type expr: Constructor: int
                                                                                                                         └──Desc: Variable
                                                                                                                            └──Variable: loop
                                                                                                                      └──Expression:
                                                                                                                         └──Type expr: Constructor: list
                                                                                                                            └──Type expr: Constructor: int
                                                                                                                         └──Desc: Variable
                                                                                                                            └──Variable: till
                                                                                                                └──Expression:
                                                                                                                   └──Type expr: Constructor: int
                                                                                                                   └──Desc: Variable
                                                                                                                      └──Variable: amt
                                                                                                          └──Expression:
                                                                                                             └──Type expr: Constructor: list
                                                                                                                └──Type expr: Constructor: int
                                                                                                             └──Desc: Variable
                                                                                                                └──Variable: chg
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Constructor: list
                                                                                                          └──Type expr: Constructor: list
                                                                                                             └──Type expr: Constructor: int
                                                                                                       └──Desc: Variable
                                                                                                          └──Variable: chgs
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Constructor: list
                                              └──Type expr: Constructor: int
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: int
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: int
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: int
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: int
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: int
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: int
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: int
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: int
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: loop
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: till
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: amt
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Nil
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: int
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: int |}]

let%expect_test "" =
  let str = 
    {|
      type vehicle = 
        | Bike
        | Motorbike
        | Car
        | Lorry
      ;;

      let _ = Motorbike;;

      let wheels = 
        fun t -> 
          match t with
          ( Bike -> 2
          | Motorbike -> 2
          | Car -> 4
          | Lorry -> 18
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
             └──Type name: vehicle
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Bike
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: vehicle
                └──Constructor declaration:
                   └──Constructor name: Motorbike
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: vehicle
                └──Constructor declaration:
                   └──Constructor name: Car
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: vehicle
                └──Constructor declaration:
                   └──Constructor name: Lorry
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: vehicle
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: vehicle
                   └──Desc: Any
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: vehicle
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Motorbike
                            └──Constructor type:
                               └──Type expr: Constructor: vehicle
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: vehicle
                      └──Type expr: Constructor: int
                   └──Desc: Variable: wheels
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: vehicle
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: vehicle
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: vehicle
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: vehicle
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: vehicle
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Bike
                                              └──Constructor type:
                                                 └──Type expr: Constructor: vehicle
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 2
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: vehicle
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Motorbike
                                              └──Constructor type:
                                                 └──Type expr: Constructor: vehicle
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 2
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: vehicle
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Car
                                              └──Constructor type:
                                                 └──Type expr: Constructor: vehicle
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 4
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: vehicle
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Lorry
                                              └──Constructor type:
                                                 └──Type expr: Constructor: vehicle
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 18 |}]

let%expect_test "" =
  let str = 
    {|
      type vehicle = 
        | Bike
        | Motorbike of int (* engine size in CCs *)
        | Car of bool (* true if a Reliant Robin *)
        | Lorry of int (* number of wheels *)
      ;;

      let wheels = 
        fun t ->
          match t with
          ( Bike -> 2
          | Motorbike _ -> 2
          | Car is_robin -> if is_robin then 3 else 4
          | Lorry w -> w
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
             └──Type name: vehicle
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Bike
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: vehicle
                └──Constructor declaration:
                   └──Constructor name: Motorbike
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: vehicle
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: int
                └──Constructor declaration:
                   └──Constructor name: Car
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: vehicle
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: bool
                └──Constructor declaration:
                   └──Constructor name: Lorry
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: vehicle
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: int
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: vehicle
                      └──Type expr: Constructor: int
                   └──Desc: Variable: wheels
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: vehicle
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: vehicle
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: vehicle
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: vehicle
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: vehicle
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Bike
                                              └──Constructor type:
                                                 └──Type expr: Constructor: vehicle
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 2
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: vehicle
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Motorbike
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: int
                                              └──Constructor type:
                                                 └──Type expr: Constructor: vehicle
                                           └──Pattern:
                                              └──Type expr: Constructor: int
                                              └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 2
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: vehicle
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Car
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: bool
                                              └──Constructor type:
                                                 └──Type expr: Constructor: vehicle
                                           └──Pattern:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Variable: is_robin
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: If
                                           └──Expression:
                                              └──Type expr: Constructor: bool
                                              └──Desc: Variable
                                                 └──Variable: is_robin
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 3
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 4
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: vehicle
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Lorry
                                              └──Constructor argument type:
                                                 └──Type expr: Constructor: int
                                              └──Constructor type:
                                                 └──Type expr: Constructor: vehicle
                                           └──Pattern:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable: w
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Variable
                                           └──Variable: w |}]

let%expect_test "" =
  let str = 
    {|
      exception Failure;;

      exception No_change of int;;

      external raise : 'a. exn -> 'a = "%raise";;

      let _ = raise Failure;;

      external print_endline : string -> unit = "%print_endline";;

      let _ = 
        try
          (print_endline "pre exception";
          raise (No_change 1);
          print_endline "post exception")
        with
          ( No_change _ ->
              print_endline "handled a No_change exception" 
          )
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Exception
          └──Type exception:
             └──Extension constructor:
                └──Extension name: exn
                └──Extension parameters:
                └──Extension constructor kind: Declaration
                   └──Constructor declaration:
                      └──Constructor name: Failure
                      └──Constructor alphas:
                      └──Constructor type:
                         └──Type expr: Constructor: exn
       └──Structure item: Exception
          └──Type exception:
             └──Extension constructor:
                └──Extension name: exn
                └──Extension parameters:
                └──Extension constructor kind: Declaration
                   └──Constructor declaration:
                      └──Constructor name: No_change
                      └──Constructor alphas:
                      └──Constructor type:
                         └──Type expr: Constructor: exn
                      └──Constructor argument:
                         └──Constructor betas:
                         └──Type expr: Constructor: int
       └──Structure item: Primitive
          └──Value description:
             └──Name: raise
             └──Scheme:
                └──Variables: a22967
                └──Type expr: Arrow
                   └──Type expr: Constructor: exn
                   └──Type expr: Variable: a22967
             └──Primitive name: %raise
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Variable: a22972
                   └──Desc: Any
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Variable: a22972
                      └──Desc: Application
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: exn
                               └──Type expr: Variable: a22972
                            └──Desc: Variable
                               └──Variable: raise
                               └──Type expr: Variable: a22972
                         └──Expression:
                            └──Type expr: Constructor: exn
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Failure
                                  └──Constructor type:
                                     └──Type expr: Constructor: exn
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
                   └──Type expr: Constructor: unit
                   └──Desc: Any
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: unit
                      └──Desc: Try
                         └──Expression:
                            └──Type expr: Constructor: unit
                            └──Desc: Sequence
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
                                        └──Desc: Constant: pre exception
                               └──Expression:
                                  └──Type expr: Constructor: unit
                                  └──Desc: Sequence
                                     └──Expression:
                                        └──Type expr: Constructor: unit
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: exn
                                                 └──Type expr: Constructor: unit
                                              └──Desc: Variable
                                                 └──Variable: raise
                                                 └──Type expr: Constructor: unit
                                           └──Expression:
                                              └──Type expr: Constructor: exn
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: No_change
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: int
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: exn
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 1
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
                                              └──Desc: Constant: post exception
                         └──Cases:
                            └──Case:
                               └──Pattern:
                                  └──Type expr: Constructor: exn
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: No_change
                                        └──Constructor argument type:
                                           └──Type expr: Constructor: int
                                        └──Constructor type:
                                           └──Type expr: Constructor: exn
                                     └──Pattern:
                                        └──Type expr: Constructor: int
                                        └──Desc: Any
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
                                        └──Desc: Constant: handled a No_change exception |}]

let%expect_test "" =
  let str = 
    {|
      type 'a option = 
        | None
        | Some of 'a
      ;;

      let x = Some 1;;

      let y = None;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
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
                   └──Type expr: Constructor: option
                      └──Type expr: Constructor: int
                   └──Desc: Variable: x
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: option
                         └──Type expr: Constructor: int
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Some
                            └──Constructor argument type:
                               └──Type expr: Constructor: int
                            └──Constructor type:
                               └──Type expr: Constructor: option
                                  └──Type expr: Constructor: int
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Constant: 1
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: option
                      └──Type expr: Variable: a23041
                   └──Desc: Variable: y
                └──Abstraction:
                   └──Variables: a23041
                   └──Expression:
                      └──Type expr: Constructor: option
                         └──Type expr: Variable: a23041
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: None
                            └──Constructor type:
                               └──Type expr: Constructor: option
                                  └──Type expr: Variable: a23041 |}]

let%expect_test "" =
  let str = 
    {|
      type 'a list =
        | Nil
        | Cons of 'a * 'a list
      ;;

      external raise : 'a. exn -> 'a = "%raise";;
      external lt : 'a. 'a -> 'a -> bool = "%less_than";;

      exception No_change of int;;

      let rec change = 
        fun till amt ->
          match (till, amt) with
          ( (_, 0) -> Nil
          | (Nil, amt) -> raise (No_change amt)
          | (Cons (c, till), amt) ->
              if lt amt c 
                then raise (No_change amt)
                else try Cons (c, change (Cons (c, till)) (amt - c))
                     with (No_change _ -> change till amt)
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
             └──Type name: list
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Nil
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: a
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a
       └──Structure item: Primitive
          └──Value description:
             └──Name: raise
             └──Scheme:
                └──Variables: a23044
                └──Type expr: Arrow
                   └──Type expr: Constructor: exn
                   └──Type expr: Variable: a23044
             └──Primitive name: %raise
       └──Structure item: Primitive
          └──Value description:
             └──Name: lt
             └──Scheme:
                └──Variables: a23049
                └──Type expr: Arrow
                   └──Type expr: Variable: a23049
                   └──Type expr: Arrow
                      └──Type expr: Variable: a23049
                      └──Type expr: Constructor: bool
             └──Primitive name: %less_than
       └──Structure item: Exception
          └──Type exception:
             └──Extension constructor:
                └──Extension name: exn
                └──Extension parameters:
                └──Extension constructor kind: Declaration
                   └──Constructor declaration:
                      └──Constructor name: No_change
                      └──Constructor alphas:
                      └──Constructor type:
                         └──Type expr: Constructor: exn
                      └──Constructor argument:
                         └──Constructor betas:
                         └──Type expr: Constructor: int
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: change
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: list
                            └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Constructor: int
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: int
                            └──Desc: Variable: till
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Constructor: list
                                  └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable: amt
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Constructor: int
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: list
                                              └──Type expr: Constructor: int
                                           └──Type expr: Constructor: int
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: till
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: amt
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: list
                                           └──Type expr: Constructor: int
                                        └──Type expr: Constructor: int
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Any
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 0
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: int
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: int
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Nil
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable: amt
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: int
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: exn
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: raise
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: int
                                                 └──Expression:
                                                    └──Type expr: Constructor: exn
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: No_change
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: exn
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: amt
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Cons
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable: c
                                                             └──Pattern:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: int
                                                                └──Desc: Variable: till
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable: amt
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: int
                                              └──Desc: If
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
                                                                └──Desc: Variable
                                                                   └──Variable: lt
                                                                   └──Type expr: Constructor: int
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: amt
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: c
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: exn
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: raise
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                       └──Expression:
                                                          └──Type expr: Constructor: exn
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: No_change
                                                                └──Constructor argument type:
                                                                   └──Type expr: Constructor: int
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: exn
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: amt
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Try
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Cons
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: int
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: int
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: int
                                                             └──Expression:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: int
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: int
                                                                └──Desc: Tuple
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Variable
                                                                         └──Variable: c
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: int
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: int
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: int
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Constructor: int
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: int
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Constructor: int
                                                                                  └──Desc: Variable
                                                                                     └──Variable: change
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: list
                                                                                     └──Type expr: Constructor: int
                                                                                  └──Desc: Construct
                                                                                     └──Constructor description:
                                                                                        └──Name: Cons
                                                                                        └──Constructor argument type:
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Constructor: int
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Constructor: int
                                                                                        └──Constructor type:
                                                                                           └──Type expr: Constructor: list
                                                                                              └──Type expr: Constructor: int
                                                                                     └──Expression:
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Constructor: int
                                                                                           └──Type expr: Constructor: list
                                                                                              └──Type expr: Constructor: int
                                                                                        └──Desc: Tuple
                                                                                           └──Expression:
                                                                                              └──Type expr: Constructor: int
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: c
                                                                                           └──Expression:
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Constructor: int
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: till
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
                                                                                        └──Desc: Primitive: (-)
                                                                                     └──Expression:
                                                                                        └──Type expr: Constructor: int
                                                                                        └──Desc: Variable
                                                                                           └──Variable: amt
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: int
                                                                                  └──Desc: Variable
                                                                                     └──Variable: c
                                                       └──Cases:
                                                          └──Case:
                                                             └──Pattern:
                                                                └──Type expr: Constructor: exn
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: No_change
                                                                      └──Constructor argument type:
                                                                         └──Type expr: Constructor: int
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: exn
                                                                   └──Pattern:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Any
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: int
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: int
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: int
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: int
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: int
                                                                                  └──Type expr: Constructor: list
                                                                                     └──Type expr: Constructor: int
                                                                            └──Desc: Variable
                                                                               └──Variable: change
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: int
                                                                            └──Desc: Variable
                                                                               └──Variable: till
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Variable
                                                                         └──Variable: amt |}]

let%expect_test "" =
  let str = 
    {|
      type shape = 
        | Null
        | Circle of float (* radius *)
        | Join of shape * shape
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: shape
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Null
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: shape
                └──Constructor declaration:
                   └──Constructor name: Circle
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: shape
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Constructor: float
                └──Constructor declaration:
                   └──Constructor name: Join
                   └──Constructor alphas:
                   └──Constructor type:
                      └──Type expr: Constructor: shape
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Constructor: shape
                         └──Type expr: Constructor: shape |}]

let%expect_test "" =
  let str = 
    {|
      type 'a tree = 
        | Lf
        | Br of 'a tree * 'a * 'a tree
      ;;

      type 'a list =
        | Nil
        | Cons of 'a * 'a list
      ;;

      external append : 'a. 'a list -> 'a list -> 'a list = "%append";;

      let rec pre_order = 
        fun t ->
          match t with
          ( Lf -> Nil
          | Br (l, x, r) ->
            append (Cons (x, Nil)) 
              (append (pre_order l) (pre_order r))
          )
      ;;

      let rec in_order = 
        fun t ->
          match t with
          ( Lf -> Nil
          | Br (l, x, r) ->
            append (pre_order l)
              (append (Cons (x, Nil)) (pre_order r))
          )
      ;;

      let rec post_order = 
        fun t ->
          match t with
          ( Lf -> Nil
          | Br (l, x, r) ->
            append (post_order l)
              ( append (post_order r) (Cons (x, Nil)) )  
          )
      ;;

      let in_order = fun t ->
        let rec loop = 
          fun t acc ->
            match t with
            ( Lf -> acc
            | Br (l, x, r) -> 
              loop l (Cons (x, loop r acc))
            )
        in loop t
      ;;

      let pre_order = fun t ->
        let rec loop = 
          fun t acc ->
            match t with
            ( Lf -> acc
            | Br (l, x, r) ->
              Cons (x, loop l (loop r acc))
            )
        in loop t
      ;;

      let post_order = fun t ->
        let rec loop = 
          fun t acc ->
            match t with
            ( Lf -> acc
            | Br (l, x, r) ->
              loop l (loop r (Cons (x, acc)))  
            )
        in loop t
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Type
          └──Type declaration:
             └──Type name: tree
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Lf
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: tree
                         └──Type expr: Variable: a
                └──Constructor declaration:
                   └──Constructor name: Br
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: tree
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Constructor: tree
                            └──Type expr: Variable: a
                         └──Type expr: Variable: a
                         └──Type expr: Constructor: tree
                            └──Type expr: Variable: a
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
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: a
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a
       └──Structure item: Primitive
          └──Value description:
             └──Name: append
             └──Scheme:
                └──Variables: a23191
                └──Type expr: Arrow
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: a23191
                   └──Type expr: Arrow
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a23191
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a23191
             └──Primitive name: %append
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: pre_order
                └──Abstraction:
                   └──Variables: a23251
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: tree
                            └──Type expr: Variable: a23251
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a23251
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: tree
                               └──Type expr: Variable: a23251
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a23251
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: tree
                                     └──Type expr: Variable: a23251
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: tree
                                  └──Type expr: Variable: a23251
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: tree
                                           └──Type expr: Variable: a23251
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Lf
                                              └──Constructor type:
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a23251
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Variable: a23251
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Nil
                                              └──Constructor type:
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: a23251
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: tree
                                           └──Type expr: Variable: a23251
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Br
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a23251
                                                    └──Type expr: Variable: a23251
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a23251
                                              └──Constructor type:
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a23251
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a23251
                                                 └──Type expr: Variable: a23251
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a23251
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a23251
                                                    └──Desc: Variable: l
                                                 └──Pattern:
                                                    └──Type expr: Variable: a23251
                                                    └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a23251
                                                    └──Desc: Variable: r
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Variable: a23251
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: a23251
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: a23251
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a23251
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a23251
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a23251
                                                    └──Desc: Variable
                                                       └──Variable: append
                                                       └──Type expr: Variable: a23251
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a23251
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Cons
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a23251
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a23251
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a23251
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a23251
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a23251
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Variable: a23251
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a23251
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Nil
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Variable: a23251
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a23251
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a23251
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a23251
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a23251
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a23251
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a23251
                                                          └──Desc: Variable
                                                             └──Variable: append
                                                             └──Type expr: Variable: a23251
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a23251
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: tree
                                                                      └──Type expr: Variable: a23251
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: a23251
                                                                └──Desc: Variable
                                                                   └──Variable: pre_order
                                                             └──Expression:
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a23251
                                                                └──Desc: Variable
                                                                   └──Variable: l
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a23251
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a23251
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a23251
                                                          └──Desc: Variable
                                                             └──Variable: pre_order
                                                       └──Expression:
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a23251
                                                          └──Desc: Variable
                                                             └──Variable: r
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: in_order
                └──Abstraction:
                   └──Variables: a23343
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: tree
                            └──Type expr: Variable: a23343
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a23343
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: tree
                               └──Type expr: Variable: a23343
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a23343
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: tree
                                     └──Type expr: Variable: a23343
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: tree
                                  └──Type expr: Variable: a23343
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: tree
                                           └──Type expr: Variable: a23343
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Lf
                                              └──Constructor type:
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a23343
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Variable: a23343
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Nil
                                              └──Constructor type:
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: a23343
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: tree
                                           └──Type expr: Variable: a23343
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Br
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a23343
                                                    └──Type expr: Variable: a23343
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a23343
                                              └──Constructor type:
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a23343
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a23343
                                                 └──Type expr: Variable: a23343
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a23343
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a23343
                                                    └──Desc: Variable: l
                                                 └──Pattern:
                                                    └──Type expr: Variable: a23343
                                                    └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a23343
                                                    └──Desc: Variable: r
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Variable: a23343
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: a23343
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: a23343
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a23343
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a23343
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a23343
                                                    └──Desc: Variable
                                                       └──Variable: append
                                                       └──Type expr: Variable: a23343
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a23343
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a23343
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a23343
                                                          └──Desc: Variable
                                                             └──Variable: pre_order
                                                             └──Type expr: Variable: a23343
                                                       └──Expression:
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a23343
                                                          └──Desc: Variable
                                                             └──Variable: l
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a23343
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a23343
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a23343
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a23343
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a23343
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a23343
                                                          └──Desc: Variable
                                                             └──Variable: append
                                                             └──Type expr: Variable: a23343
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a23343
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Cons
                                                                └──Constructor argument type:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a23343
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Variable: a23343
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: a23343
                                                             └──Expression:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a23343
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: a23343
                                                                └──Desc: Tuple
                                                                   └──Expression:
                                                                      └──Type expr: Variable: a23343
                                                                      └──Desc: Variable
                                                                         └──Variable: x
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Variable: a23343
                                                                      └──Desc: Construct
                                                                         └──Constructor description:
                                                                            └──Name: Nil
                                                                            └──Constructor type:
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Variable: a23343
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a23343
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a23343
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a23343
                                                          └──Desc: Variable
                                                             └──Variable: pre_order
                                                             └──Type expr: Variable: a23343
                                                       └──Expression:
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a23343
                                                          └──Desc: Variable
                                                             └──Variable: r
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: post_order
                └──Abstraction:
                   └──Variables: a23423
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: tree
                            └──Type expr: Variable: a23423
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a23423
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: tree
                               └──Type expr: Variable: a23423
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a23423
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: tree
                                     └──Type expr: Variable: a23423
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: tree
                                  └──Type expr: Variable: a23423
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: tree
                                           └──Type expr: Variable: a23423
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Lf
                                              └──Constructor type:
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a23423
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Variable: a23423
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Nil
                                              └──Constructor type:
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: a23423
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: tree
                                           └──Type expr: Variable: a23423
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Br
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a23423
                                                    └──Type expr: Variable: a23423
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a23423
                                              └──Constructor type:
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a23423
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a23423
                                                 └──Type expr: Variable: a23423
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a23423
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a23423
                                                    └──Desc: Variable: l
                                                 └──Pattern:
                                                    └──Type expr: Variable: a23423
                                                    └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a23423
                                                    └──Desc: Variable: r
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Variable: a23423
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: a23423
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: a23423
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a23423
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a23423
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a23423
                                                    └──Desc: Variable
                                                       └──Variable: append
                                                       └──Type expr: Variable: a23423
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a23423
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a23423
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a23423
                                                          └──Desc: Variable
                                                             └──Variable: post_order
                                                       └──Expression:
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a23423
                                                          └──Desc: Variable
                                                             └──Variable: l
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a23423
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a23423
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a23423
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a23423
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a23423
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a23423
                                                          └──Desc: Variable
                                                             └──Variable: append
                                                             └──Type expr: Variable: a23423
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a23423
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: tree
                                                                      └──Type expr: Variable: a23423
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: a23423
                                                                └──Desc: Variable
                                                                   └──Variable: post_order
                                                             └──Expression:
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a23423
                                                                └──Desc: Variable
                                                                   └──Variable: r
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a23423
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Cons
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a23423
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a23423
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a23423
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a23423
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a23423
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Variable: a23423
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a23423
                                                                └──Desc: Construct
                                                                   └──Constructor description:
                                                                      └──Name: Nil
                                                                      └──Constructor type:
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Variable: a23423
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: tree
                         └──Type expr: Variable: a23488
                      └──Type expr: Arrow
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a23488
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a23488
                   └──Desc: Variable: in_order
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: tree
                            └──Type expr: Variable: a23488
                         └──Type expr: Arrow
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a23488
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a23488
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: tree
                               └──Type expr: Variable: a23488
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a23488
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a23488
                            └──Desc: Let rec
                               └──Value bindings:
                                  └──Value binding:
                                     └──Variable: loop
                                     └──Abstraction:
                                        └──Variables: a23465
                                        └──Expression:
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Variable: a23465
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: a23465
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: a23465
                                           └──Desc: Function
                                              └──Pattern:
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a23465
                                                 └──Desc: Variable: t
                                              └──Expression:
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a23465
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a23465
                                                 └──Desc: Function
                                                    └──Pattern:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a23465
                                                       └──Desc: Variable: acc
                                                    └──Expression:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a23465
                                                       └──Desc: Match
                                                          └──Expression:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a23465
                                                             └──Desc: Variable
                                                                └──Variable: t
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a23465
                                                          └──Cases:
                                                             └──Case:
                                                                └──Pattern:
                                                                   └──Type expr: Constructor: tree
                                                                      └──Type expr: Variable: a23465
                                                                   └──Desc: Construct
                                                                      └──Constructor description:
                                                                         └──Name: Lf
                                                                         └──Constructor type:
                                                                            └──Type expr: Constructor: tree
                                                                               └──Type expr: Variable: a23465
                                                                └──Expression:
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: a23465
                                                                   └──Desc: Variable
                                                                      └──Variable: acc
                                                             └──Case:
                                                                └──Pattern:
                                                                   └──Type expr: Constructor: tree
                                                                      └──Type expr: Variable: a23465
                                                                   └──Desc: Construct
                                                                      └──Constructor description:
                                                                         └──Name: Br
                                                                         └──Constructor argument type:
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Constructor: tree
                                                                                  └──Type expr: Variable: a23465
                                                                               └──Type expr: Variable: a23465
                                                                               └──Type expr: Constructor: tree
                                                                                  └──Type expr: Variable: a23465
                                                                         └──Constructor type:
                                                                            └──Type expr: Constructor: tree
                                                                               └──Type expr: Variable: a23465
                                                                      └──Pattern:
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Constructor: tree
                                                                               └──Type expr: Variable: a23465
                                                                            └──Type expr: Variable: a23465
                                                                            └──Type expr: Constructor: tree
                                                                               └──Type expr: Variable: a23465
                                                                         └──Desc: Tuple
                                                                            └──Pattern:
                                                                               └──Type expr: Constructor: tree
                                                                                  └──Type expr: Variable: a23465
                                                                               └──Desc: Variable: l
                                                                            └──Pattern:
                                                                               └──Type expr: Variable: a23465
                                                                               └──Desc: Variable: x
                                                                            └──Pattern:
                                                                               └──Type expr: Constructor: tree
                                                                                  └──Type expr: Variable: a23465
                                                                               └──Desc: Variable: r
                                                                └──Expression:
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: a23465
                                                                   └──Desc: Application
                                                                      └──Expression:
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: a23465
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: a23465
                                                                         └──Desc: Application
                                                                            └──Expression:
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: tree
                                                                                     └──Type expr: Variable: a23465
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Variable: a23465
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Variable: a23465
                                                                               └──Desc: Variable
                                                                                  └──Variable: loop
                                                                            └──Expression:
                                                                               └──Type expr: Constructor: tree
                                                                                  └──Type expr: Variable: a23465
                                                                               └──Desc: Variable
                                                                                  └──Variable: l
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Variable: a23465
                                                                         └──Desc: Construct
                                                                            └──Constructor description:
                                                                               └──Name: Cons
                                                                               └──Constructor argument type:
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a23465
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Variable: a23465
                                                                               └──Constructor type:
                                                                                  └──Type expr: Constructor: list
                                                                                     └──Type expr: Variable: a23465
                                                                            └──Expression:
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: a23465
                                                                                  └──Type expr: Constructor: list
                                                                                     └──Type expr: Variable: a23465
                                                                               └──Desc: Tuple
                                                                                  └──Expression:
                                                                                     └──Type expr: Variable: a23465
                                                                                     └──Desc: Variable
                                                                                        └──Variable: x
                                                                                  └──Expression:
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Variable: a23465
                                                                                     └──Desc: Application
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Variable: a23465
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Variable: a23465
                                                                                           └──Desc: Application
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Constructor: tree
                                                                                                       └──Type expr: Variable: a23465
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Constructor: list
                                                                                                          └──Type expr: Variable: a23465
                                                                                                       └──Type expr: Constructor: list
                                                                                                          └──Type expr: Variable: a23465
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: loop
                                                                                              └──Expression:
                                                                                                 └──Type expr: Constructor: tree
                                                                                                    └──Type expr: Variable: a23465
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: r
                                                                                        └──Expression:
                                                                                           └──Type expr: Constructor: list
                                                                                              └──Type expr: Variable: a23465
                                                                                           └──Desc: Variable
                                                                                              └──Variable: acc
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: a23488
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: a23488
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: tree
                                              └──Type expr: Variable: a23488
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a23488
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a23488
                                        └──Desc: Variable
                                           └──Variable: loop
                                           └──Type expr: Variable: a23488
                                     └──Expression:
                                        └──Type expr: Constructor: tree
                                           └──Type expr: Variable: a23488
                                        └──Desc: Variable
                                           └──Variable: t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: tree
                         └──Type expr: Variable: a23553
                      └──Type expr: Arrow
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a23553
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a23553
                   └──Desc: Variable: pre_order
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: tree
                            └──Type expr: Variable: a23553
                         └──Type expr: Arrow
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a23553
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a23553
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: tree
                               └──Type expr: Variable: a23553
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a23553
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a23553
                            └──Desc: Let rec
                               └──Value bindings:
                                  └──Value binding:
                                     └──Variable: loop
                                     └──Abstraction:
                                        └──Variables: a23523
                                        └──Expression:
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Variable: a23523
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: a23523
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: a23523
                                           └──Desc: Function
                                              └──Pattern:
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a23523
                                                 └──Desc: Variable: t
                                              └──Expression:
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a23523
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a23523
                                                 └──Desc: Function
                                                    └──Pattern:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a23523
                                                       └──Desc: Variable: acc
                                                    └──Expression:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a23523
                                                       └──Desc: Match
                                                          └──Expression:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a23523
                                                             └──Desc: Variable
                                                                └──Variable: t
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a23523
                                                          └──Cases:
                                                             └──Case:
                                                                └──Pattern:
                                                                   └──Type expr: Constructor: tree
                                                                      └──Type expr: Variable: a23523
                                                                   └──Desc: Construct
                                                                      └──Constructor description:
                                                                         └──Name: Lf
                                                                         └──Constructor type:
                                                                            └──Type expr: Constructor: tree
                                                                               └──Type expr: Variable: a23523
                                                                └──Expression:
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: a23523
                                                                   └──Desc: Variable
                                                                      └──Variable: acc
                                                             └──Case:
                                                                └──Pattern:
                                                                   └──Type expr: Constructor: tree
                                                                      └──Type expr: Variable: a23523
                                                                   └──Desc: Construct
                                                                      └──Constructor description:
                                                                         └──Name: Br
                                                                         └──Constructor argument type:
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Constructor: tree
                                                                                  └──Type expr: Variable: a23523
                                                                               └──Type expr: Variable: a23523
                                                                               └──Type expr: Constructor: tree
                                                                                  └──Type expr: Variable: a23523
                                                                         └──Constructor type:
                                                                            └──Type expr: Constructor: tree
                                                                               └──Type expr: Variable: a23523
                                                                      └──Pattern:
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Constructor: tree
                                                                               └──Type expr: Variable: a23523
                                                                            └──Type expr: Variable: a23523
                                                                            └──Type expr: Constructor: tree
                                                                               └──Type expr: Variable: a23523
                                                                         └──Desc: Tuple
                                                                            └──Pattern:
                                                                               └──Type expr: Constructor: tree
                                                                                  └──Type expr: Variable: a23523
                                                                               └──Desc: Variable: l
                                                                            └──Pattern:
                                                                               └──Type expr: Variable: a23523
                                                                               └──Desc: Variable: x
                                                                            └──Pattern:
                                                                               └──Type expr: Constructor: tree
                                                                                  └──Type expr: Variable: a23523
                                                                               └──Desc: Variable: r
                                                                └──Expression:
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: a23523
                                                                   └──Desc: Construct
                                                                      └──Constructor description:
                                                                         └──Name: Cons
                                                                         └──Constructor argument type:
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a23523
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Variable: a23523
                                                                         └──Constructor type:
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: a23523
                                                                      └──Expression:
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a23523
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: a23523
                                                                         └──Desc: Tuple
                                                                            └──Expression:
                                                                               └──Type expr: Variable: a23523
                                                                               └──Desc: Variable
                                                                                  └──Variable: x
                                                                            └──Expression:
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Variable: a23523
                                                                               └──Desc: Application
                                                                                  └──Expression:
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Variable: a23523
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Variable: a23523
                                                                                     └──Desc: Application
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Constructor: tree
                                                                                                 └──Type expr: Variable: a23523
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Variable: a23523
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Variable: a23523
                                                                                           └──Desc: Variable
                                                                                              └──Variable: loop
                                                                                        └──Expression:
                                                                                           └──Type expr: Constructor: tree
                                                                                              └──Type expr: Variable: a23523
                                                                                           └──Desc: Variable
                                                                                              └──Variable: l
                                                                                  └──Expression:
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Variable: a23523
                                                                                     └──Desc: Application
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Variable: a23523
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Variable: a23523
                                                                                           └──Desc: Application
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Constructor: tree
                                                                                                       └──Type expr: Variable: a23523
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Constructor: list
                                                                                                          └──Type expr: Variable: a23523
                                                                                                       └──Type expr: Constructor: list
                                                                                                          └──Type expr: Variable: a23523
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: loop
                                                                                              └──Expression:
                                                                                                 └──Type expr: Constructor: tree
                                                                                                    └──Type expr: Variable: a23523
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: r
                                                                                        └──Expression:
                                                                                           └──Type expr: Constructor: list
                                                                                              └──Type expr: Variable: a23523
                                                                                           └──Desc: Variable
                                                                                              └──Variable: acc
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: a23553
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: a23553
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: tree
                                              └──Type expr: Variable: a23553
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a23553
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a23553
                                        └──Desc: Variable
                                           └──Variable: loop
                                           └──Type expr: Variable: a23553
                                     └──Expression:
                                        └──Type expr: Constructor: tree
                                           └──Type expr: Variable: a23553
                                        └──Desc: Variable
                                           └──Variable: t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: tree
                         └──Type expr: Variable: a23618
                      └──Type expr: Arrow
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a23618
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a23618
                   └──Desc: Variable: post_order
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: tree
                            └──Type expr: Variable: a23618
                         └──Type expr: Arrow
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a23618
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a23618
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: tree
                               └──Type expr: Variable: a23618
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a23618
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a23618
                            └──Desc: Let rec
                               └──Value bindings:
                                  └──Value binding:
                                     └──Variable: loop
                                     └──Abstraction:
                                        └──Variables: a23602
                                        └──Expression:
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Variable: a23602
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: a23602
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: a23602
                                           └──Desc: Function
                                              └──Pattern:
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a23602
                                                 └──Desc: Variable: t
                                              └──Expression:
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a23602
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a23602
                                                 └──Desc: Function
                                                    └──Pattern:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a23602
                                                       └──Desc: Variable: acc
                                                    └──Expression:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a23602
                                                       └──Desc: Match
                                                          └──Expression:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a23602
                                                             └──Desc: Variable
                                                                └──Variable: t
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a23602
                                                          └──Cases:
                                                             └──Case:
                                                                └──Pattern:
                                                                   └──Type expr: Constructor: tree
                                                                      └──Type expr: Variable: a23602
                                                                   └──Desc: Construct
                                                                      └──Constructor description:
                                                                         └──Name: Lf
                                                                         └──Constructor type:
                                                                            └──Type expr: Constructor: tree
                                                                               └──Type expr: Variable: a23602
                                                                └──Expression:
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: a23602
                                                                   └──Desc: Variable
                                                                      └──Variable: acc
                                                             └──Case:
                                                                └──Pattern:
                                                                   └──Type expr: Constructor: tree
                                                                      └──Type expr: Variable: a23602
                                                                   └──Desc: Construct
                                                                      └──Constructor description:
                                                                         └──Name: Br
                                                                         └──Constructor argument type:
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Constructor: tree
                                                                                  └──Type expr: Variable: a23602
                                                                               └──Type expr: Variable: a23602
                                                                               └──Type expr: Constructor: tree
                                                                                  └──Type expr: Variable: a23602
                                                                         └──Constructor type:
                                                                            └──Type expr: Constructor: tree
                                                                               └──Type expr: Variable: a23602
                                                                      └──Pattern:
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Constructor: tree
                                                                               └──Type expr: Variable: a23602
                                                                            └──Type expr: Variable: a23602
                                                                            └──Type expr: Constructor: tree
                                                                               └──Type expr: Variable: a23602
                                                                         └──Desc: Tuple
                                                                            └──Pattern:
                                                                               └──Type expr: Constructor: tree
                                                                                  └──Type expr: Variable: a23602
                                                                               └──Desc: Variable: l
                                                                            └──Pattern:
                                                                               └──Type expr: Variable: a23602
                                                                               └──Desc: Variable: x
                                                                            └──Pattern:
                                                                               └──Type expr: Constructor: tree
                                                                                  └──Type expr: Variable: a23602
                                                                               └──Desc: Variable: r
                                                                └──Expression:
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: a23602
                                                                   └──Desc: Application
                                                                      └──Expression:
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: a23602
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: a23602
                                                                         └──Desc: Application
                                                                            └──Expression:
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: tree
                                                                                     └──Type expr: Variable: a23602
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Variable: a23602
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Variable: a23602
                                                                               └──Desc: Variable
                                                                                  └──Variable: loop
                                                                            └──Expression:
                                                                               └──Type expr: Constructor: tree
                                                                                  └──Type expr: Variable: a23602
                                                                               └──Desc: Variable
                                                                                  └──Variable: l
                                                                      └──Expression:
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Variable: a23602
                                                                         └──Desc: Application
                                                                            └──Expression:
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: list
                                                                                     └──Type expr: Variable: a23602
                                                                                  └──Type expr: Constructor: list
                                                                                     └──Type expr: Variable: a23602
                                                                               └──Desc: Application
                                                                                  └──Expression:
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Constructor: tree
                                                                                           └──Type expr: Variable: a23602
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Constructor: list
                                                                                              └──Type expr: Variable: a23602
                                                                                           └──Type expr: Constructor: list
                                                                                              └──Type expr: Variable: a23602
                                                                                     └──Desc: Variable
                                                                                        └──Variable: loop
                                                                                  └──Expression:
                                                                                     └──Type expr: Constructor: tree
                                                                                        └──Type expr: Variable: a23602
                                                                                     └──Desc: Variable
                                                                                        └──Variable: r
                                                                            └──Expression:
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Variable: a23602
                                                                               └──Desc: Construct
                                                                                  └──Constructor description:
                                                                                     └──Name: Cons
                                                                                     └──Constructor argument type:
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: a23602
                                                                                           └──Type expr: Constructor: list
                                                                                              └──Type expr: Variable: a23602
                                                                                     └──Constructor type:
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Variable: a23602
                                                                                  └──Expression:
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Variable: a23602
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Variable: a23602
                                                                                     └──Desc: Tuple
                                                                                        └──Expression:
                                                                                           └──Type expr: Variable: a23602
                                                                                           └──Desc: Variable
                                                                                              └──Variable: x
                                                                                        └──Expression:
                                                                                           └──Type expr: Constructor: list
                                                                                              └──Type expr: Variable: a23602
                                                                                           └──Desc: Variable
                                                                                              └──Variable: acc
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: a23618
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: a23618
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Constructor: tree
                                              └──Type expr: Variable: a23618
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a23618
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a23618
                                        └──Desc: Variable
                                           └──Variable: loop
                                           └──Type expr: Variable: a23618
                                     └──Expression:
                                        └──Type expr: Constructor: tree
                                           └──Type expr: Variable: a23618
                                        └──Desc: Variable
                                           └──Variable: t |}]

let%expect_test "" =
  let str = 
    {|
      type 'a list =
        | Nil
        | Cons of 'a * 'a list
      ;;

      let _ = 
        Cons (fun n -> n * 2, Cons (fun n -> n * 3, Cons (fun n -> n + 1, Nil)))
      ;;

      let _ = 
        fun n -> n * 2
      ;;

      let _ = 
        (fun n -> n * 2) 17
      ;;

      let double = fun n -> n * 2;;

      let _ = 
        fun x -> match x with (0 -> true | _ -> false)
      ;;

      let is_zero = 
        fun x -> match x with (0 -> true | _ -> false)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
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
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: a
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: list
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: int
                   └──Desc: Any
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: list
                         └──Type expr: Arrow
                            └──Type expr: Constructor: int
                            └──Type expr: Constructor: int
                      └──Desc: Construct
                         └──Constructor description:
                            └──Name: Cons
                            └──Constructor argument type:
                               └──Type expr: Tuple
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                                  └──Type expr: Constructor: list
                                     └──Type expr: Arrow
                                        └──Type expr: Constructor: int
                                        └──Type expr: Constructor: int
                            └──Constructor type:
                               └──Type expr: Constructor: list
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                         └──Expression:
                            └──Type expr: Tuple
                               └──Type expr: Arrow
                                  └──Type expr: Constructor: int
                                  └──Type expr: Constructor: int
                               └──Type expr: Constructor: list
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                            └──Desc: Tuple
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Constructor: int
                                     └──Type expr: Constructor: int
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Constructor: int
                                        └──Desc: Variable: n
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
                                                    └──Desc: Primitive: (*)
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: n
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 2
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Arrow
                                        └──Type expr: Constructor: int
                                        └──Type expr: Constructor: int
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Cons
                                        └──Constructor argument type:
                                           └──Type expr: Tuple
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: int
                                        └──Constructor type:
                                           └──Type expr: Constructor: list
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Arrow
                                              └──Type expr: Constructor: int
                                              └──Type expr: Constructor: int
                                           └──Type expr: Constructor: list
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: int
                                              └──Desc: Function
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable: n
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
                                                                └──Desc: Primitive: (*)
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: n
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Constant: 3
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: int
                                                    └──Type expr: Constructor: int
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: int
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: int
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: int
                                                          └──Type expr: Constructor: int
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: int
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Function
                                                             └──Pattern:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable: n
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
                                                                            └──Desc: Variable
                                                                               └──Variable: n
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Constant: 1
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: int
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Nil
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: int
                                                                         └──Type expr: Constructor: int
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: int
                      └──Type expr: Constructor: int
                   └──Desc: Any
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: n
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
                                        └──Desc: Primitive: (*)
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Variable
                                           └──Variable: n
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Constant: 2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Constructor: int
                   └──Desc: Any
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Constructor: int
                      └──Desc: Application
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable: n
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
                                              └──Desc: Primitive: (*)
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: n
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 2
                         └──Expression:
                            └──Type expr: Constructor: int
                            └──Desc: Constant: 17
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: int
                      └──Type expr: Constructor: int
                   └──Desc: Variable: double
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: n
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
                                        └──Desc: Primitive: (*)
                                     └──Expression:
                                        └──Type expr: Constructor: int
                                        └──Desc: Variable
                                           └──Variable: n
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Constant: 2
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: int
                      └──Type expr: Constructor: bool
                   └──Desc: Any
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: bool
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: x
                               └──Type expr: Constructor: int
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 0
                                     └──Expression:
                                        └──Type expr: Constructor: bool
                                        └──Desc: Constant: true
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: int
                                        └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Constructor: bool
                                        └──Desc: Constant: false
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: int
                      └──Type expr: Constructor: bool
                   └──Desc: Variable: is_zero
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Constructor: bool
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable
                                     └──Variable: x
                               └──Type expr: Constructor: int
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: int
                                        └──Desc: Constant: 0
                                     └──Expression:
                                        └──Type expr: Constructor: bool
                                        └──Desc: Constant: true
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: int
                                        └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Constructor: bool
                                        └──Desc: Constant: false |}]

let%expect_test "" =
  let str = 
    {|
      type 'a list =
        | Nil
        | Cons of 'a * 'a list
      ;;

      external map : 'a 'b. ('a -> 'b) -> 'a list -> 'b list = "%map";;
      external hd : 'a. 'a list -> 'a = "%hd";;
      external tl : 'a. 'a list -> 'a list = "%tl";;

      let rec transpose = 
        fun t ->
          match t with
          ( Cons (Nil, _) -> Nil
          | rows ->
            Cons (map hd rows, transpose (map tl rows))
          )
      ;;

      let rec dot_product = 
        fun xs ys ->
          match (xs, ys) with
          ( (Nil, Nil) -> 0
          | (Cons (x, xs), Cons (y, ys)) ->
              (x * y) + dot_product xs ys
          )
      ;;

      let rec product = 
        fun a b ->
          let c = transpose b in
          map (fun rows -> map (dot_product rows) c) a
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    Structure:
    └──Structure:
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
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: a
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a
       └──Structure item: Primitive
          └──Value description:
             └──Name: map
             └──Scheme:
                └──Variables: a23823,a23822
                └──Type expr: Arrow
                   └──Type expr: Arrow
                      └──Type expr: Variable: a23822
                      └──Type expr: Variable: a23823
                   └──Type expr: Arrow
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a23822
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a23823
             └──Primitive name: %map
       └──Structure item: Primitive
          └──Value description:
             └──Name: hd
             └──Scheme:
                └──Variables: a23834
                └──Type expr: Arrow
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: a23834
                   └──Type expr: Variable: a23834
             └──Primitive name: %hd
       └──Structure item: Primitive
          └──Value description:
             └──Name: tl
             └──Scheme:
                └──Variables: a23839
                └──Type expr: Arrow
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: a23839
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: a23839
             └──Primitive name: %tl
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: transpose
                └──Abstraction:
                   └──Variables: a23889
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: list
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a23889
                         └──Type expr: Constructor: list
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a23889
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a23889
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a23889
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: a23889
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: list
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: a23889
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a23889
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Cons
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a23889
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a23889
                                              └──Constructor type:
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a23889
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: a23889
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a23889
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a23889
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Nil
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a23889
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a23889
                                                    └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a23889
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Nil
                                              └──Constructor type:
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a23889
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a23889
                                        └──Desc: Variable: rows
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a23889
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Cons
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a23889
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a23889
                                              └──Constructor type:
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a23889
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: a23889
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a23889
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a23889
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a23889
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a23889
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Variable: a23889
                                                                      └──Type expr: Variable: a23889
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Variable: a23889
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Variable: a23889
                                                                └──Desc: Variable
                                                                   └──Variable: map
                                                                   └──Type expr: Variable: a23889
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: a23889
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: a23889
                                                                   └──Type expr: Variable: a23889
                                                                └──Desc: Variable
                                                                   └──Variable: hd
                                                                   └──Type expr: Variable: a23889
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a23889
                                                          └──Desc: Variable
                                                             └──Variable: rows
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a23889
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a23889
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Variable: a23889
                                                          └──Desc: Variable
                                                             └──Variable: transpose
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Variable: a23889
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Variable: a23889
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Variable: a23889
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: a23889
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Variable: a23889
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Variable: a23889
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Variable: a23889
                                                                      └──Desc: Variable
                                                                         └──Variable: map
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Variable: a23889
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Variable: a23889
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Variable: a23889
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Variable: a23889
                                                                      └──Desc: Variable
                                                                         └──Variable: tl
                                                                         └──Type expr: Variable: a23889
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: a23889
                                                                └──Desc: Variable
                                                                   └──Variable: rows
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: dot_product
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: list
                            └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: int
                            └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: int
                            └──Desc: Variable: xs
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: list
                                  └──Type expr: Constructor: int
                               └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Constructor: int
                                  └──Desc: Variable: ys
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: list
                                              └──Type expr: Constructor: int
                                           └──Type expr: Constructor: list
                                              └──Type expr: Constructor: int
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: xs
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: ys
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: list
                                           └──Type expr: Constructor: int
                                        └──Type expr: Constructor: list
                                           └──Type expr: Constructor: int
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: int
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Nil
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Nil
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 0
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: int
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Cons
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable: x
                                                             └──Pattern:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: int
                                                                └──Desc: Variable: xs
                                                 └──Pattern:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Cons
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: int
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: int
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Variable: y
                                                             └──Pattern:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: int
                                                                └──Desc: Variable: ys
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
                                                                      └──Desc: Primitive: (*)
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
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: int
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: int
                                                                      └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: dot_product
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: xs
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: ys
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: product
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: list
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: int
                         └──Type expr: Arrow
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: list
                                  └──Type expr: Constructor: int
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: list
                                  └──Type expr: Constructor: int
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: list
                                  └──Type expr: Constructor: int
                            └──Desc: Variable: a
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: list
                                  └──Type expr: Constructor: list
                                     └──Type expr: Constructor: int
                               └──Type expr: Constructor: list
                                  └──Type expr: Constructor: list
                                     └──Type expr: Constructor: int
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Constructor: list
                                        └──Type expr: Constructor: int
                                  └──Desc: Variable: b
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Constructor: list
                                        └──Type expr: Constructor: int
                                  └──Desc: Let
                                     └──Value bindings:
                                        └──Value binding:
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: int
                                              └──Desc: Variable: c
                                           └──Abstraction:
                                              └──Variables:
                                              └──Expression:
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                                 └──Desc: Application
                                                    └──Expression:
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                       └──Desc: Variable
                                                          └──Variable: transpose
                                                          └──Type expr: Constructor: int
                                                    └──Expression:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: int
                                                       └──Desc: Variable
                                                          └──Variable: b
                                     └──Expression:
                                        └──Type expr: Constructor: list
                                           └──Type expr: Constructor: list
                                              └──Type expr: Constructor: int
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: int
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: int
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: int
                                                       └──Type expr: Arrow
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: map
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: int
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: int
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: int
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: int
                                                    └──Desc: Function
                                                       └──Pattern:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Variable: rows
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: int
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: int
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: int
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: int
                                                                            └──Type expr: Constructor: int
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: int
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: int
                                                                      └──Desc: Variable
                                                                         └──Variable: map
                                                                         └──Type expr: Constructor: int
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: int
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: list
                                                                            └──Type expr: Constructor: int
                                                                         └──Type expr: Constructor: int
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: int
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: list
                                                                                     └──Type expr: Constructor: int
                                                                                  └──Type expr: Constructor: int
                                                                            └──Desc: Variable
                                                                               └──Variable: dot_product
                                                                         └──Expression:
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: int
                                                                            └──Desc: Variable
                                                                               └──Variable: rows
                                                             └──Expression:
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: int
                                                                └──Desc: Variable
                                                                   └──Variable: c
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: a |}]

let%expect_test "" =
  let str = 
    {|
      type 'a tree = 
        | Lf
        | Br of 'a tree * 'a * 'a tree
      ;;

      let rec cons = 
        fun t x ->
          match t with
          ( Lf -> Br (Lf, x, Lf)
          | Br (l, y, r) ->
              Br (cons l y, x, r)  
          )
      ;;

      external raise : 'a. exn -> 'a = "%raise";;

      exception Invalid_argument of string;;

      let rec uncons =
        fun t -> 
          match t with
          ( Lf -> raise (Invalid_argument "uncons")
          | Br (Lf, x, Lf) -> (x, Lf)
          | Br (l, x, r) ->
            let (y, l') = uncons l in
            (x, Br (r, x, l'))
          )
      ;;

      let hd = fun t ->
        let (x, _) = uncons t in x
      ;;

      let tl = fun t ->
        let (_, t) = uncons t in t
      ;;

      external mod : int -> int -> int = "%mod";;

      let even = fun n -> mod n 2 = 0;;

      let rec nth = 
        fun t n ->
          match (t, n) with
          ( (Lf, _) -> raise (Invalid_argument "nth")
          | (Br (_, x, _), 0) -> x
          | (Br (l, x, r), n) ->
              if even n then nth r (n / 2)
              else nth l (n / 2)
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
             └──Type name: tree
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Lf
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: tree
                         └──Type expr: Variable: a
                └──Constructor declaration:
                   └──Constructor name: Br
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: tree
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Constructor: tree
                            └──Type expr: Variable: a
                         └──Type expr: Variable: a
                         └──Type expr: Constructor: tree
                            └──Type expr: Variable: a
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: cons
                └──Abstraction:
                   └──Variables: a24128
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: tree
                            └──Type expr: Variable: a24128
                         └──Type expr: Arrow
                            └──Type expr: Variable: a24128
                            └──Type expr: Constructor: tree
                               └──Type expr: Variable: a24128
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: tree
                               └──Type expr: Variable: a24128
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a24128
                               └──Type expr: Constructor: tree
                                  └──Type expr: Variable: a24128
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: a24128
                                  └──Desc: Variable: x
                               └──Expression:
                                  └──Type expr: Constructor: tree
                                     └──Type expr: Variable: a24128
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: tree
                                           └──Type expr: Variable: a24128
                                        └──Desc: Variable
                                           └──Variable: t
                                     └──Type expr: Constructor: tree
                                        └──Type expr: Variable: a24128
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Variable: a24128
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Lf
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: a24128
                                           └──Expression:
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Variable: a24128
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Br
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a24128
                                                          └──Type expr: Variable: a24128
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a24128
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: a24128
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: a24128
                                                       └──Type expr: Variable: a24128
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: a24128
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a24128
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Lf
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: tree
                                                                      └──Type expr: Variable: a24128
                                                       └──Expression:
                                                          └──Type expr: Variable: a24128
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a24128
                                                          └──Desc: Construct
                                                             └──Constructor description:
                                                                └──Name: Lf
                                                                └──Constructor type:
                                                                   └──Type expr: Constructor: tree
                                                                      └──Type expr: Variable: a24128
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Variable: a24128
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Br
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a24128
                                                          └──Type expr: Variable: a24128
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a24128
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: a24128
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: a24128
                                                       └──Type expr: Variable: a24128
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: a24128
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a24128
                                                          └──Desc: Variable: l
                                                       └──Pattern:
                                                          └──Type expr: Variable: a24128
                                                          └──Desc: Variable: y
                                                       └──Pattern:
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a24128
                                                          └──Desc: Variable: r
                                           └──Expression:
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Variable: a24128
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Br
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a24128
                                                          └──Type expr: Variable: a24128
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a24128
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: a24128
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: a24128
                                                       └──Type expr: Variable: a24128
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: a24128
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a24128
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: a24128
                                                                   └──Type expr: Constructor: tree
                                                                      └──Type expr: Variable: a24128
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: tree
                                                                            └──Type expr: Variable: a24128
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Variable: a24128
                                                                            └──Type expr: Constructor: tree
                                                                               └──Type expr: Variable: a24128
                                                                      └──Desc: Variable
                                                                         └──Variable: cons
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: tree
                                                                         └──Type expr: Variable: a24128
                                                                      └──Desc: Variable
                                                                         └──Variable: l
                                                             └──Expression:
                                                                └──Type expr: Variable: a24128
                                                                └──Desc: Variable
                                                                   └──Variable: y
                                                       └──Expression:
                                                          └──Type expr: Variable: a24128
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a24128
                                                          └──Desc: Variable
                                                             └──Variable: r
       └──Structure item: Primitive
          └──Value description:
             └──Name: raise
             └──Scheme:
                └──Variables: a24136
                └──Type expr: Arrow
                   └──Type expr: Constructor: exn
                   └──Type expr: Variable: a24136
             └──Primitive name: %raise
       └──Structure item: Exception
          └──Type exception:
             └──Extension constructor:
                └──Extension name: exn
                └──Extension parameters:
                └──Extension constructor kind: Declaration
                   └──Constructor declaration:
                      └──Constructor name: Invalid_argument
                      └──Constructor alphas:
                      └──Constructor type:
                         └──Type expr: Constructor: exn
                      └──Constructor argument:
                         └──Constructor betas:
                         └──Type expr: Constructor: string
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: uncons
                └──Abstraction:
                   └──Variables: a24216
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: tree
                            └──Type expr: Variable: a24216
                         └──Type expr: Tuple
                            └──Type expr: Variable: a24216
                            └──Type expr: Constructor: tree
                               └──Type expr: Variable: a24216
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: tree
                               └──Type expr: Variable: a24216
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Tuple
                               └──Type expr: Variable: a24216
                               └──Type expr: Constructor: tree
                                  └──Type expr: Variable: a24216
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Constructor: tree
                                     └──Type expr: Variable: a24216
                                  └──Desc: Variable
                                     └──Variable: t
                               └──Type expr: Constructor: tree
                                  └──Type expr: Variable: a24216
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: tree
                                           └──Type expr: Variable: a24216
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Lf
                                              └──Constructor type:
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a24216
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a24216
                                           └──Type expr: Constructor: tree
                                              └──Type expr: Variable: a24216
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: exn
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a24216
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a24216
                                              └──Desc: Variable
                                                 └──Variable: raise
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a24216
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a24216
                                           └──Expression:
                                              └──Type expr: Constructor: exn
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Invalid_argument
                                                    └──Constructor argument type:
                                                       └──Type expr: Constructor: string
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: exn
                                                 └──Expression:
                                                    └──Type expr: Constructor: string
                                                    └──Desc: Constant: uncons
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: tree
                                           └──Type expr: Variable: a24216
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Br
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a24216
                                                    └──Type expr: Variable: a24216
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a24216
                                              └──Constructor type:
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a24216
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a24216
                                                 └──Type expr: Variable: a24216
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a24216
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a24216
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Lf
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a24216
                                                 └──Pattern:
                                                    └──Type expr: Variable: a24216
                                                    └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a24216
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Lf
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a24216
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a24216
                                           └──Type expr: Constructor: tree
                                              └──Type expr: Variable: a24216
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Variable: a24216
                                              └──Desc: Variable
                                                 └──Variable: x
                                           └──Expression:
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Variable: a24216
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Lf
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: a24216
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Constructor: tree
                                           └──Type expr: Variable: a24216
                                        └──Desc: Construct
                                           └──Constructor description:
                                              └──Name: Br
                                              └──Constructor argument type:
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a24216
                                                    └──Type expr: Variable: a24216
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a24216
                                              └──Constructor type:
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a24216
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a24216
                                                 └──Type expr: Variable: a24216
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a24216
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a24216
                                                    └──Desc: Variable: l
                                                 └──Pattern:
                                                    └──Type expr: Variable: a24216
                                                    └──Desc: Variable: x
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a24216
                                                    └──Desc: Variable: r
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a24216
                                           └──Type expr: Constructor: tree
                                              └──Type expr: Variable: a24216
                                        └──Desc: Let
                                           └──Value bindings:
                                              └──Value binding:
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a24216
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: a24216
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Variable: a24216
                                                          └──Desc: Variable: y
                                                       └──Pattern:
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a24216
                                                          └──Desc: Variable: l'
                                                 └──Abstraction:
                                                    └──Variables:
                                                    └──Expression:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a24216
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a24216
                                                       └──Desc: Application
                                                          └──Expression:
                                                             └──Type expr: Arrow
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a24216
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a24216
                                                                   └──Type expr: Constructor: tree
                                                                      └──Type expr: Variable: a24216
                                                             └──Desc: Variable
                                                                └──Variable: uncons
                                                          └──Expression:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a24216
                                                             └──Desc: Variable
                                                                └──Variable: l
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a24216
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a24216
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Variable: a24216
                                                    └──Desc: Variable
                                                       └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a24216
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Br
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a24216
                                                                └──Type expr: Variable: a24216
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a24216
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a24216
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a24216
                                                             └──Type expr: Variable: a24216
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a24216
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a24216
                                                                └──Desc: Variable
                                                                   └──Variable: r
                                                             └──Expression:
                                                                └──Type expr: Variable: a24216
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a24216
                                                                └──Desc: Variable
                                                                   └──Variable: l'
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: tree
                         └──Type expr: Variable: a24233
                      └──Type expr: Variable: a24233
                   └──Desc: Variable: hd
                └──Abstraction:
                   └──Variables: a24233,a24233,a24233
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: tree
                            └──Type expr: Variable: a24233
                         └──Type expr: Variable: a24233
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: tree
                               └──Type expr: Variable: a24233
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Variable: a24233
                            └──Desc: Let
                               └──Value bindings:
                                  └──Value binding:
                                     └──Pattern:
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a24233
                                           └──Type expr: Constructor: tree
                                              └──Type expr: Variable: a24233
                                        └──Desc: Tuple
                                           └──Pattern:
                                              └──Type expr: Variable: a24233
                                              └──Desc: Variable: x
                                           └──Pattern:
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Variable: a24233
                                              └──Desc: Any
                                     └──Abstraction:
                                        └──Variables:
                                        └──Expression:
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a24233
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Variable: a24233
                                           └──Desc: Application
                                              └──Expression:
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a24233
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a24233
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: a24233
                                                 └──Desc: Variable
                                                    └──Variable: uncons
                                                    └──Type expr: Variable: a24233
                                              └──Expression:
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a24233
                                                 └──Desc: Variable
                                                    └──Variable: t
                               └──Expression:
                                  └──Type expr: Variable: a24233
                                  └──Desc: Variable
                                     └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: tree
                         └──Type expr: Variable: a24256
                      └──Type expr: Constructor: tree
                         └──Type expr: Variable: a24256
                   └──Desc: Variable: tl
                └──Abstraction:
                   └──Variables: a24256,a24256
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: tree
                            └──Type expr: Variable: a24256
                         └──Type expr: Constructor: tree
                            └──Type expr: Variable: a24256
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: tree
                               └──Type expr: Variable: a24256
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Constructor: tree
                               └──Type expr: Variable: a24256
                            └──Desc: Let
                               └──Value bindings:
                                  └──Value binding:
                                     └──Pattern:
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a24256
                                           └──Type expr: Constructor: tree
                                              └──Type expr: Variable: a24256
                                        └──Desc: Tuple
                                           └──Pattern:
                                              └──Type expr: Variable: a24256
                                              └──Desc: Any
                                           └──Pattern:
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Variable: a24256
                                              └──Desc: Variable: t
                                     └──Abstraction:
                                        └──Variables:
                                        └──Expression:
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a24256
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Variable: a24256
                                           └──Desc: Application
                                              └──Expression:
                                                 └──Type expr: Arrow
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a24256
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a24256
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: a24256
                                                 └──Desc: Variable
                                                    └──Variable: uncons
                                                    └──Type expr: Variable: a24256
                                              └──Expression:
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a24256
                                                 └──Desc: Variable
                                                    └──Variable: t
                               └──Expression:
                                  └──Type expr: Constructor: tree
                                     └──Type expr: Variable: a24256
                                  └──Desc: Variable
                                     └──Variable: t
       └──Structure item: Primitive
          └──Value description:
             └──Name: mod
             └──Scheme:
                └──Variables:
                └──Type expr: Arrow
                   └──Type expr: Constructor: int
                   └──Type expr: Arrow
                      └──Type expr: Constructor: int
                      └──Type expr: Constructor: int
             └──Primitive name: %mod
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Constructor: int
                      └──Type expr: Constructor: bool
                   └──Desc: Variable: even
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: int
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: int
                            └──Desc: Variable: n
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
                                                       └──Variable: mod
                                                 └──Expression:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable
                                                       └──Variable: n
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Constant: 2
                               └──Expression:
                                  └──Type expr: Constructor: int
                                  └──Desc: Constant: 0
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: nth
                └──Abstraction:
                   └──Variables: a24368
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Constructor: tree
                            └──Type expr: Variable: a24368
                         └──Type expr: Arrow
                            └──Type expr: Constructor: int
                            └──Type expr: Variable: a24368
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Constructor: tree
                               └──Type expr: Variable: a24368
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Constructor: int
                               └──Type expr: Variable: a24368
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Constructor: int
                                  └──Desc: Variable: n
                               └──Expression:
                                  └──Type expr: Variable: a24368
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: tree
                                              └──Type expr: Variable: a24368
                                           └──Type expr: Constructor: int
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Variable: a24368
                                              └──Desc: Variable
                                                 └──Variable: t
                                           └──Expression:
                                              └──Type expr: Constructor: int
                                              └──Desc: Variable
                                                 └──Variable: n
                                     └──Type expr: Tuple
                                        └──Type expr: Constructor: tree
                                           └──Type expr: Variable: a24368
                                        └──Type expr: Constructor: int
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a24368
                                                 └──Type expr: Constructor: int
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a24368
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Lf
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a24368
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Any
                                           └──Expression:
                                              └──Type expr: Variable: a24368
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: exn
                                                       └──Type expr: Variable: a24368
                                                    └──Desc: Variable
                                                       └──Variable: raise
                                                       └──Type expr: Variable: a24368
                                                 └──Expression:
                                                    └──Type expr: Constructor: exn
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Invalid_argument
                                                          └──Constructor argument type:
                                                             └──Type expr: Constructor: string
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: exn
                                                       └──Expression:
                                                          └──Type expr: Constructor: string
                                                          └──Desc: Constant: nth
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a24368
                                                 └──Type expr: Constructor: int
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a24368
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Br
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a24368
                                                                └──Type expr: Variable: a24368
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a24368
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a24368
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a24368
                                                             └──Type expr: Variable: a24368
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a24368
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a24368
                                                                └──Desc: Any
                                                             └──Pattern:
                                                                └──Type expr: Variable: a24368
                                                                └──Desc: Variable: x
                                                             └──Pattern:
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a24368
                                                                └──Desc: Any
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Constant: 0
                                           └──Expression:
                                              └──Type expr: Variable: a24368
                                              └──Desc: Variable
                                                 └──Variable: x
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a24368
                                                 └──Type expr: Constructor: int
                                              └──Desc: Tuple
                                                 └──Pattern:
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a24368
                                                    └──Desc: Construct
                                                       └──Constructor description:
                                                          └──Name: Br
                                                          └──Constructor argument type:
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a24368
                                                                └──Type expr: Variable: a24368
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a24368
                                                          └──Constructor type:
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a24368
                                                       └──Pattern:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a24368
                                                             └──Type expr: Variable: a24368
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a24368
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a24368
                                                                └──Desc: Variable: l
                                                             └──Pattern:
                                                                └──Type expr: Variable: a24368
                                                                └──Desc: Variable: x
                                                             └──Pattern:
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a24368
                                                                └──Desc: Variable: r
                                                 └──Pattern:
                                                    └──Type expr: Constructor: int
                                                    └──Desc: Variable: n
                                           └──Expression:
                                              └──Type expr: Variable: a24368
                                              └──Desc: If
                                                 └──Expression:
                                                    └──Type expr: Constructor: bool
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Constructor: bool
                                                          └──Desc: Variable
                                                             └──Variable: even
                                                       └──Expression:
                                                          └──Type expr: Constructor: int
                                                          └──Desc: Variable
                                                             └──Variable: n
                                                 └──Expression:
                                                    └──Type expr: Variable: a24368
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Variable: a24368
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: tree
                                                                      └──Type expr: Variable: a24368
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: int
                                                                      └──Type expr: Variable: a24368
                                                                └──Desc: Variable
                                                                   └──Variable: nth
                                                             └──Expression:
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a24368
                                                                └──Desc: Variable
                                                                   └──Variable: r
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
                                                                      └──Desc: Primitive: (/)
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Variable
                                                                         └──Variable: n
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Constant: 2
                                                 └──Expression:
                                                    └──Type expr: Variable: a24368
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Constructor: int
                                                             └──Type expr: Variable: a24368
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Constructor: tree
                                                                      └──Type expr: Variable: a24368
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Constructor: int
                                                                      └──Type expr: Variable: a24368
                                                                └──Desc: Variable
                                                                   └──Variable: nth
                                                             └──Expression:
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a24368
                                                                └──Desc: Variable
                                                                   └──Variable: l
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
                                                                      └──Desc: Primitive: (/)
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: int
                                                                      └──Desc: Variable
                                                                         └──Variable: n
                                                             └──Expression:
                                                                └──Type expr: Constructor: int
                                                                └──Desc: Constant: 2 |}]

let%expect_test "" =
  let str = 
    {|
      type 'a tree = 
        | Lf
        | Br of 'a tree * 'a * 'a tree
      ;;

      type 'a list =
        | Nil
        | Cons of 'a * 'a list
      ;;

      external raise : 'a. exn -> 'a = "%raise";;
      exception Empty;;

      type 'a queue = 'a list * 'a list;;
      let empty = (Nil, Nil);;

      let is_empty = fun q ->
        match q with
        ( (Nil, Nil) -> true
        | _ -> false)
      ;;

      external rev : 'a. 'a list -> 'a list = "%rev";;

      let norm = fun q ->
        match q with
        ( (Nil, ys) -> (rev ys, Nil)
        | q -> q
        )
      ;;

      let enqueue = fun (xs, ys) y -> norm (xs, Cons (y, ys));;
      let dequeue = fun q ->
        match q with
        ( (Cons (x, xs), ys) -> norm (xs, ys)
        | _ -> raise Empty
        )
      ;;

      let hd = fun q ->
        match q with
        ( (Cons (x, _), _) -> x
        | _ -> raise Empty
        )
      ;;

      let rec bfs = fun q -> 
        if is_empty q then Nil
        else
          match hd q with
          ( Lf -> bfs (dequeue q)
          | Br (l, x, r) ->
            Cons (x, bfs (enqueue (enqueue (dequeue q) l) r) ) 
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
             └──Type name: tree
             └──Type declaration kind: Variant
                └──Constructor declaration:
                   └──Constructor name: Lf
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: tree
                         └──Type expr: Variable: a
                └──Constructor declaration:
                   └──Constructor name: Br
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: tree
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Constructor: tree
                            └──Type expr: Variable: a
                         └──Type expr: Variable: a
                         └──Type expr: Constructor: tree
                            └──Type expr: Variable: a
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
                └──Constructor declaration:
                   └──Constructor name: Cons
                   └──Constructor alphas: a
                   └──Constructor type:
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
                   └──Constructor argument:
                      └──Constructor betas:
                      └──Type expr: Tuple
                         └──Type expr: Variable: a
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a
       └──Structure item: Primitive
          └──Value description:
             └──Name: raise
             └──Scheme:
                └──Variables: a24442
                └──Type expr: Arrow
                   └──Type expr: Constructor: exn
                   └──Type expr: Variable: a24442
             └──Primitive name: %raise
       └──Structure item: Exception
          └──Type exception:
             └──Extension constructor:
                └──Extension name: exn
                └──Extension parameters:
                └──Extension constructor kind: Declaration
                   └──Constructor declaration:
                      └──Constructor name: Empty
                      └──Constructor alphas:
                      └──Constructor type:
                         └──Type expr: Constructor: exn
       └──Structure item: Type
          └──Type declaration:
             └──Type name: queue
             └──Type declaration kind: Alias
                └──Alias
                   └──Alias name: queue
                   └──Alias alphas: a
                   └──Type expr: Tuple
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Tuple
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a24452
                      └──Type expr: Constructor: list
                         └──Type expr: Variable: a24455
                   └──Desc: Variable: empty
                └──Abstraction:
                   └──Variables: a24455,a24452
                   └──Expression:
                      └──Type expr: Tuple
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a24452
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a24455
                      └──Desc: Tuple
                         └──Expression:
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a24452
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Nil
                                  └──Constructor type:
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: a24452
                         └──Expression:
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a24455
                            └──Desc: Construct
                               └──Constructor description:
                                  └──Name: Nil
                                  └──Constructor type:
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: a24455
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Tuple
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a24468
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a24465
                      └──Type expr: Constructor: bool
                   └──Desc: Variable: is_empty
                └──Abstraction:
                   └──Variables: a24465,a24468
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Tuple
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a24468
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a24465
                         └──Type expr: Constructor: bool
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Tuple
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a24468
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a24465
                            └──Desc: Variable: q
                         └──Expression:
                            └──Type expr: Constructor: bool
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Tuple
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: a24468
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: a24465
                                  └──Desc: Variable
                                     └──Variable: q
                               └──Type expr: Tuple
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: a24468
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: a24465
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24468
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24465
                                        └──Desc: Tuple
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a24468
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a24468
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a24465
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a24465
                                     └──Expression:
                                        └──Type expr: Constructor: bool
                                        └──Desc: Constant: true
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24468
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24465
                                        └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Constructor: bool
                                        └──Desc: Constant: false
       └──Structure item: Primitive
          └──Value description:
             └──Name: rev
             └──Scheme:
                └──Variables: a24478
                └──Type expr: Arrow
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: a24478
                   └──Type expr: Constructor: list
                      └──Type expr: Variable: a24478
             └──Primitive name: %rev
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Tuple
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a24509
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a24509
                      └──Type expr: Tuple
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a24509
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a24509
                   └──Desc: Variable: norm
                └──Abstraction:
                   └──Variables: a24509
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Tuple
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a24509
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a24509
                         └──Type expr: Tuple
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a24509
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a24509
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Tuple
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a24509
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a24509
                            └──Desc: Variable: q
                         └──Expression:
                            └──Type expr: Tuple
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a24509
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a24509
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Tuple
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: a24509
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: a24509
                                  └──Desc: Variable
                                     └──Variable: q
                               └──Type expr: Tuple
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: a24509
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: a24509
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24509
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24509
                                        └──Desc: Tuple
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a24509
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a24509
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a24509
                                              └──Desc: Variable: ys
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24509
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24509
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a24509
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a24509
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a24509
                                                    └──Desc: Variable
                                                       └──Variable: rev
                                                       └──Type expr: Variable: a24509
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a24509
                                                    └──Desc: Variable
                                                       └──Variable: ys
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a24509
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Nil
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a24509
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24509
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24509
                                        └──Desc: Variable: q
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24509
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24509
                                        └──Desc: Variable
                                           └──Variable: q
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Tuple
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a24537
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a24537
                      └──Type expr: Arrow
                         └──Type expr: Variable: a24537
                         └──Type expr: Tuple
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a24537
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a24537
                   └──Desc: Variable: enqueue
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Tuple
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a24537
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a24537
                         └──Type expr: Arrow
                            └──Type expr: Variable: a24537
                            └──Type expr: Tuple
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a24537
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a24537
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Tuple
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a24537
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a24537
                            └──Desc: Tuple
                               └──Pattern:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: a24537
                                  └──Desc: Variable: xs
                               └──Pattern:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: a24537
                                  └──Desc: Variable: ys
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a24537
                               └──Type expr: Tuple
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: a24537
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: a24537
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: a24537
                                  └──Desc: Variable: y
                               └──Expression:
                                  └──Type expr: Tuple
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: a24537
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: a24537
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Tuple
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a24537
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a24537
                                           └──Type expr: Tuple
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a24537
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a24537
                                        └──Desc: Variable
                                           └──Variable: norm
                                           └──Type expr: Variable: a24537
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24537
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24537
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a24537
                                              └──Desc: Variable
                                                 └──Variable: xs
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a24537
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a24537
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a24537
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a24537
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a24537
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a24537
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Variable: a24537
                                                          └──Desc: Variable
                                                             └──Variable: y
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a24537
                                                          └──Desc: Variable
                                                             └──Variable: ys
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Tuple
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a24556
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a24575
                      └──Type expr: Tuple
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a24575
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a24575
                   └──Desc: Variable: dequeue
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Tuple
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a24556
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a24575
                         └──Type expr: Tuple
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a24575
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a24575
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Tuple
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a24556
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a24575
                            └──Desc: Variable: q
                         └──Expression:
                            └──Type expr: Tuple
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a24575
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a24575
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Tuple
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: a24556
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: a24575
                                  └──Desc: Variable
                                     └──Variable: q
                               └──Type expr: Tuple
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: a24556
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: a24575
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24556
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24575
                                        └──Desc: Tuple
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a24556
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a24556
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a24556
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a24556
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a24556
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a24556
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Variable: a24556
                                                          └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a24556
                                                          └──Desc: Variable: xs
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a24575
                                              └──Desc: Variable: ys
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24575
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24575
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a24575
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a24575
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a24575
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a24575
                                              └──Desc: Variable
                                                 └──Variable: norm
                                                 └──Type expr: Variable: a24575
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: a24575
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Variable: a24575
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a24575
                                                    └──Desc: Variable
                                                       └──Variable: xs
                                                       └──Type expr: Variable: a24575
                                                 └──Expression:
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a24575
                                                    └──Desc: Variable
                                                       └──Variable: ys
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24556
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24575
                                        └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24575
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24575
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: exn
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a24575
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a24575
                                              └──Desc: Variable
                                                 └──Variable: raise
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a24575
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Variable: a24575
                                           └──Expression:
                                              └──Type expr: Constructor: exn
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Empty
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: exn
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Tuple
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a24599
                         └──Type expr: Variable: a24597
                      └──Type expr: Variable: a24593
                   └──Desc: Variable: hd
                └──Abstraction:
                   └──Variables: a24593,a24593,a24597,a24593
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Tuple
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a24599
                            └──Type expr: Variable: a24597
                         └──Type expr: Variable: a24593
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Tuple
                               └──Type expr: Constructor: list
                                  └──Type expr: Variable: a24599
                               └──Type expr: Variable: a24597
                            └──Desc: Variable: q
                         └──Expression:
                            └──Type expr: Variable: a24593
                            └──Desc: Match
                               └──Expression:
                                  └──Type expr: Tuple
                                     └──Type expr: Constructor: list
                                        └──Type expr: Variable: a24599
                                     └──Type expr: Variable: a24597
                                  └──Desc: Variable
                                     └──Variable: q
                               └──Type expr: Tuple
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: a24599
                                  └──Type expr: Variable: a24597
                               └──Cases:
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24599
                                           └──Type expr: Variable: a24597
                                        └──Desc: Tuple
                                           └──Pattern:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a24599
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a24599
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a24599
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a24599
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a24599
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a24599
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Variable: a24599
                                                          └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a24599
                                                          └──Desc: Any
                                           └──Pattern:
                                              └──Type expr: Variable: a24597
                                              └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Variable: a24593
                                        └──Desc: Variable
                                           └──Variable: x
                                           └──Type expr: Variable: a24593
                                  └──Case:
                                     └──Pattern:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24599
                                           └──Type expr: Variable: a24597
                                        └──Desc: Any
                                     └──Expression:
                                        └──Type expr: Variable: a24593
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Constructor: exn
                                                 └──Type expr: Variable: a24593
                                              └──Desc: Variable
                                                 └──Variable: raise
                                                 └──Type expr: Variable: a24593
                                           └──Expression:
                                              └──Type expr: Constructor: exn
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Empty
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: exn
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: bfs
                └──Abstraction:
                   └──Variables: a24682
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Tuple
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: tree
                                  └──Type expr: Variable: a24682
                            └──Type expr: Constructor: list
                               └──Type expr: Constructor: tree
                                  └──Type expr: Variable: a24682
                         └──Type expr: Constructor: list
                            └──Type expr: Variable: a24682
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Tuple
                               └──Type expr: Constructor: list
                                  └──Type expr: Constructor: tree
                                     └──Type expr: Variable: a24682
                               └──Type expr: Constructor: list
                                  └──Type expr: Constructor: tree
                                     └──Type expr: Variable: a24682
                            └──Desc: Variable: q
                         └──Expression:
                            └──Type expr: Constructor: list
                               └──Type expr: Variable: a24682
                            └──Desc: If
                               └──Expression:
                                  └──Type expr: Constructor: bool
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Tuple
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a24682
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a24682
                                           └──Type expr: Constructor: bool
                                        └──Desc: Variable
                                           └──Variable: is_empty
                                           └──Type expr: Constructor: tree
                                              └──Type expr: Variable: a24682
                                           └──Type expr: Constructor: tree
                                              └──Type expr: Variable: a24682
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Constructor: list
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Variable: a24682
                                           └──Type expr: Constructor: list
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Variable: a24682
                                        └──Desc: Variable
                                           └──Variable: q
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: a24682
                                  └──Desc: Construct
                                     └──Constructor description:
                                        └──Name: Nil
                                        └──Constructor type:
                                           └──Type expr: Constructor: list
                                              └──Type expr: Variable: a24682
                               └──Expression:
                                  └──Type expr: Constructor: list
                                     └──Type expr: Variable: a24682
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Constructor: tree
                                           └──Type expr: Variable: a24682
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Tuple
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: a24682
                                                    └──Type expr: Constructor: list
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: a24682
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a24682
                                              └──Desc: Variable
                                                 └──Variable: hd
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a24682
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a24682
                                                 └──Type expr: Constructor: tree
                                                    └──Type expr: Variable: a24682
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a24682
                                                 └──Type expr: Constructor: list
                                                    └──Type expr: Constructor: tree
                                                       └──Type expr: Variable: a24682
                                              └──Desc: Variable
                                                 └──Variable: q
                                     └──Type expr: Constructor: tree
                                        └──Type expr: Variable: a24682
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Variable: a24682
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Lf
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: a24682
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a24682
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a24682
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a24682
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a24682
                                                    └──Desc: Variable
                                                       └──Variable: bfs
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a24682
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a24682
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: tree
                                                                      └──Type expr: Variable: a24682
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: tree
                                                                      └──Type expr: Variable: a24682
                                                             └──Type expr: Tuple
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: tree
                                                                      └──Type expr: Variable: a24682
                                                                └──Type expr: Constructor: list
                                                                   └──Type expr: Constructor: tree
                                                                      └──Type expr: Variable: a24682
                                                          └──Desc: Variable
                                                             └──Variable: dequeue
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a24682
                                                             └──Type expr: Constructor: tree
                                                                └──Type expr: Variable: a24682
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a24682
                                                             └──Type expr: Constructor: list
                                                                └──Type expr: Constructor: tree
                                                                   └──Type expr: Variable: a24682
                                                          └──Desc: Variable
                                                             └──Variable: q
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Constructor: tree
                                                 └──Type expr: Variable: a24682
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Br
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a24682
                                                          └──Type expr: Variable: a24682
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a24682
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: a24682
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: a24682
                                                       └──Type expr: Variable: a24682
                                                       └──Type expr: Constructor: tree
                                                          └──Type expr: Variable: a24682
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a24682
                                                          └──Desc: Variable: l
                                                       └──Pattern:
                                                          └──Type expr: Variable: a24682
                                                          └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Constructor: tree
                                                             └──Type expr: Variable: a24682
                                                          └──Desc: Variable: r
                                           └──Expression:
                                              └──Type expr: Constructor: list
                                                 └──Type expr: Variable: a24682
                                              └──Desc: Construct
                                                 └──Constructor description:
                                                    └──Name: Cons
                                                    └──Constructor argument type:
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a24682
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a24682
                                                    └──Constructor type:
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a24682
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a24682
                                                       └──Type expr: Constructor: list
                                                          └──Type expr: Variable: a24682
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Variable: a24682
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Constructor: list
                                                             └──Type expr: Variable: a24682
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: tree
                                                                            └──Type expr: Variable: a24682
                                                                      └──Type expr: Constructor: list
                                                                         └──Type expr: Constructor: tree
                                                                            └──Type expr: Variable: a24682
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Variable: a24682
                                                                └──Desc: Variable
                                                                   └──Variable: bfs
                                                             └──Expression:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: tree
                                                                         └──Type expr: Variable: a24682
                                                                   └──Type expr: Constructor: list
                                                                      └──Type expr: Constructor: tree
                                                                         └──Type expr: Variable: a24682
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Constructor: tree
                                                                            └──Type expr: Variable: a24682
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: tree
                                                                                  └──Type expr: Variable: a24682
                                                                            └──Type expr: Constructor: list
                                                                               └──Type expr: Constructor: tree
                                                                                  └──Type expr: Variable: a24682
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Constructor: list
                                                                                     └──Type expr: Constructor: tree
                                                                                        └──Type expr: Variable: a24682
                                                                                  └──Type expr: Constructor: list
                                                                                     └──Type expr: Constructor: tree
                                                                                        └──Type expr: Variable: a24682
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Constructor: tree
                                                                                     └──Type expr: Variable: a24682
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Constructor: tree
                                                                                           └──Type expr: Variable: a24682
                                                                                     └──Type expr: Constructor: list
                                                                                        └──Type expr: Constructor: tree
                                                                                           └──Type expr: Variable: a24682
                                                                            └──Desc: Variable
                                                                               └──Variable: enqueue
                                                                               └──Type expr: Constructor: tree
                                                                                  └──Type expr: Variable: a24682
                                                                         └──Expression:
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: tree
                                                                                     └──Type expr: Variable: a24682
                                                                               └──Type expr: Constructor: list
                                                                                  └──Type expr: Constructor: tree
                                                                                     └──Type expr: Variable: a24682
                                                                            └──Desc: Application
                                                                               └──Expression:
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Constructor: tree
                                                                                        └──Type expr: Variable: a24682
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Constructor: tree
                                                                                              └──Type expr: Variable: a24682
                                                                                        └──Type expr: Constructor: list
                                                                                           └──Type expr: Constructor: tree
                                                                                              └──Type expr: Variable: a24682
                                                                                  └──Desc: Application
                                                                                     └──Expression:
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Constructor: tree
                                                                                                    └──Type expr: Variable: a24682
                                                                                              └──Type expr: Constructor: list
                                                                                                 └──Type expr: Constructor: tree
                                                                                                    └──Type expr: Variable: a24682
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Constructor: tree
                                                                                                 └──Type expr: Variable: a24682
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: tree
                                                                                                       └──Type expr: Variable: a24682
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: tree
                                                                                                       └──Type expr: Variable: a24682
                                                                                        └──Desc: Variable
                                                                                           └──Variable: enqueue
                                                                                           └──Type expr: Constructor: tree
                                                                                              └──Type expr: Variable: a24682
                                                                                     └──Expression:
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Constructor: list
                                                                                              └──Type expr: Constructor: tree
                                                                                                 └──Type expr: Variable: a24682
                                                                                           └──Type expr: Constructor: list
                                                                                              └──Type expr: Constructor: tree
                                                                                                 └──Type expr: Variable: a24682
                                                                                        └──Desc: Application
                                                                                           └──Expression:
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Tuple
                                                                                                    └──Type expr: Constructor: list
                                                                                                       └──Type expr: Constructor: tree
                                                                                                          └──Type expr: Variable: a24682
                                                                                                    └──Type expr: Constructor: list
                                                                                                       └──Type expr: Constructor: tree
                                                                                                          └──Type expr: Variable: a24682
                                                                                                 └──Type expr: Tuple
                                                                                                    └──Type expr: Constructor: list
                                                                                                       └──Type expr: Constructor: tree
                                                                                                          └──Type expr: Variable: a24682
                                                                                                    └──Type expr: Constructor: list
                                                                                                       └──Type expr: Constructor: tree
                                                                                                          └──Type expr: Variable: a24682
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: dequeue
                                                                                                 └──Type expr: Constructor: tree
                                                                                                    └──Type expr: Variable: a24682
                                                                                                 └──Type expr: Constructor: tree
                                                                                                    └──Type expr: Variable: a24682
                                                                                           └──Expression:
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: tree
                                                                                                       └──Type expr: Variable: a24682
                                                                                                 └──Type expr: Constructor: list
                                                                                                    └──Type expr: Constructor: tree
                                                                                                       └──Type expr: Variable: a24682
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: q
                                                                               └──Expression:
                                                                                  └──Type expr: Constructor: tree
                                                                                     └──Type expr: Variable: a24682
                                                                                  └──Desc: Variable
                                                                                     └──Variable: l
                                                                   └──Expression:
                                                                      └──Type expr: Constructor: tree
                                                                         └──Type expr: Variable: a24682
                                                                      └──Desc: Variable
                                                                         └──Variable: r |}]

let%expect_test "" =
  let str = 
    {|
      type 'a seq = 
        | Nil
        | Cons of 'a * (unit -> 'a seq)
      ;;

      external raise : 'a. exn -> 'a = "%raise";;
      exception Empty;;

      let hd = fun t ->
        match t with
        ( Cons (x, _) -> x
        | _ -> raise Empty
        )
      ;;

      let tl = fun t ->
        match t with
        ( Cons (_, tf) -> tf ()
        | _ -> raise Empty
        )
      ;;

      let empty = Nil

      let is_empty = fun t ->
        match t with
        ( Nil -> true
        | _ -> false
        )
      ;;

      let rec map = fun f t ->
        match t with
        ( Nil -> Nil
        | Cons (x, tf) -> Cons (f x, fun () -> map f (tf ()))
        )
      ;;

      let rec filter = fun f t ->
        match t with
        ( Nil -> Nil
        | Cons (x, tf) ->
            if f x then
              Cons (x, fun () -> filter f (tf ()))
            else
              filter f (tf ())   
        )
      ;;

      let rec append = fun t1 t2 ->
        match t1 with
        ( Nil -> t2
        | Cons (x, t1f) ->
            Cons (x, fun () -> append (t1f ()) t2)  
        ) 
      ;;

      let rec interleave = fun t1 t2 ->
        match t1 with
        ( Nil -> t2
        | Cons (x, t1f) ->
            Cons (x, fun () -> interleave t2 (t1f ()))  
        )
      ;;

      type 'a list =
        | Nil
        | Cons of 'a * 'a list
      ;;

      let rec binary_string = 
        fun bits ->
          Cons (bits, fun () -> 
            interleave
              (binary_string (Cons (0, bits)))
              (binary_string (Cons (1, bits))))
      ;;
    |}
  in
  print_infer_result str;
  [%expect {||}]
