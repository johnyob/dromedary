open! Import
open Util

(* Example from the appendix of https://www.cs.tufts.edu/~nr/cs257/archive/didier-remy/type-checking-records.pdf *)

let%expect_test "" =
  let str =
    {|
      external failwith : 'a. string -> 'a = "%failwith";;

      let rec select = fun t1 f -> 
        match t1 with
        ( `Nil -> failwith "select"
        | `Cons (x, t2) ->
            if f x then (x, t2) 
            else 
              let (y, t3) = select t2 f 
              in (y, `Cons (x, t3)) 
        )
      ;;

      let rec fold_right = fun t init f ->
        match t with
        ( `Nil -> init
        | `Cons (x, t) -> f x (fold_right t init f)
        )
      ;;

      
      let partition = fun t f ->
        fold_right t (`Nil, `Nil)
          (fun x (l, r) -> 
            if f x then (`Cons (x, l), r) else (l, `Cons (x, r)) )
      ;;

      let id = fun x -> x;;
      let compose = fun f g x -> f (g x);;

      let cons = fun x t -> `Cons (x, t);;

      let sort_append = fun f le ->
        let rec loop = fun t ->
          match t with
          ( `Nil -> id
          | `Cons (_, _) -> 
            let (pivot, t) = select t f in
            let (l, r) = partition t (fun y -> le y pivot) in
            compose (loop l) (compose (cons pivot) (loop r))
          )
        in loop
      ;;

      let sort = fun t le ->
        sort_append (fun x -> true) le t `Nil
      ;;
    |}
  in
  print_infer_result str;
  [%expect
    {|
    Structure:
    └──Structure:
       └──Structure item: Primitive
          └──Value description:
             └──Name: failwith
             └──Scheme:
                └──Variables: 0
                └──Type expr: Arrow
                   └──Type expr: Constructor: string
                   └──Type expr: Variable: 0
             └──Primitive name: %failwith
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: select
                └──Abstraction:
                   └──Variables: 86
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Mu
                            └──Variable: 87
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: 86
                                        └──Type expr: Variable: 87
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: 86
                               └──Type expr: Constructor: bool
                            └──Type expr: Tuple
                               └──Type expr: Variable: 86
                               └──Type expr: Mu
                                  └──Variable: 87
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 86
                                              └──Type expr: Variable: 87
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Mu
                               └──Variable: 87
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 86
                                           └──Type expr: Variable: 87
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                            └──Desc: Variable: t1
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 86
                                  └──Type expr: Constructor: bool
                               └──Type expr: Tuple
                                  └──Type expr: Variable: 86
                                  └──Type expr: Mu
                                     └──Variable: 87
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: 86
                                                 └──Type expr: Variable: 87
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 86
                                     └──Type expr: Constructor: bool
                                  └──Desc: Variable: f
                               └──Expression:
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: 86
                                     └──Type expr: Mu
                                        └──Variable: 87
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 86
                                                    └──Type expr: Variable: 87
                                              └──Type expr: Row cons
                                                 └──Label: Nil
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Mu
                                           └──Variable: 87
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Cons
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 86
                                                       └──Type expr: Variable: 87
                                                 └──Type expr: Row cons
                                                    └──Label: Nil
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                        └──Desc: Variable
                                           └──Variable: t1
                                     └──Type expr: Mu
                                        └──Variable: 87
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 86
                                                    └──Type expr: Variable: 87
                                              └──Type expr: Row cons
                                                 └──Label: Nil
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                     └──Cases:
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Nil
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Mu
                                                             └──Variable: 19
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 86
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Variable: 19
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                              └──Desc: Variant
                                                 └──Variant description:
                                                    └──Tag: Nil
                                                    └──Variant row:
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Mu
                                                                   └──Variable: 19
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 86
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Variable: 19
                                                                            └──Type expr: Row cons
                                                                               └──Label: Nil
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: 86
                                                 └──Type expr: Mu
                                                    └──Variable: 87
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 86
                                                                └──Type expr: Variable: 87
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Constructor: string
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 86
                                                          └──Type expr: Mu
                                                             └──Variable: 87
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 86
                                                                         └──Type expr: Variable: 87
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                    └──Desc: Variable
                                                       └──Variable: failwith
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 86
                                                          └──Type expr: Mu
                                                             └──Variable: 87
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 86
                                                                         └──Type expr: Variable: 87
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                 └──Expression:
                                                    └──Type expr: Constructor: string
                                                    └──Desc: Constant: select
                                        └──Case:
                                           └──Pattern:
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Nil
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Mu
                                                             └──Variable: 19
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 86
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Variable: 19
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                              └──Desc: Variant
                                                 └──Variant description:
                                                    └──Tag: Cons
                                                    └──Variant row:
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Mu
                                                                   └──Variable: 19
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 86
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Variable: 19
                                                                            └──Type expr: Row cons
                                                                               └──Label: Nil
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                                 └──Pattern:
                                                    └──Type expr: Mu
                                                       └──Variable: 19
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 86
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Variable: 19
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Variable: 86
                                                          └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Mu
                                                             └──Variable: 87
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 86
                                                                         └──Type expr: Variable: 87
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                          └──Desc: Variable: t2
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: 86
                                                 └──Type expr: Mu
                                                    └──Variable: 87
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 86
                                                                └──Type expr: Variable: 87
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                              └──Desc: If
                                                 └──Expression:
                                                    └──Type expr: Constructor: bool
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 86
                                                             └──Type expr: Constructor: bool
                                                          └──Desc: Variable
                                                             └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Variable: 86
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 86
                                                       └──Type expr: Mu
                                                          └──Variable: 87
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 86
                                                                      └──Type expr: Variable: 87
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Variable: 86
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Mu
                                                             └──Variable: 87
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 86
                                                                         └──Type expr: Variable: 87
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                          └──Desc: Variable
                                                             └──Variable: t2
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 86
                                                       └──Type expr: Mu
                                                          └──Variable: 87
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 86
                                                                      └──Type expr: Variable: 87
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                    └──Desc: Let
                                                       └──Value bindings:
                                                          └──Value binding:
                                                             └──Pattern:
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 86
                                                                   └──Type expr: Mu
                                                                      └──Variable: 87
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: 86
                                                                                  └──Type expr: Variable: 87
                                                                            └──Type expr: Row cons
                                                                               └──Label: Nil
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                                                                └──Desc: Tuple
                                                                   └──Pattern:
                                                                      └──Type expr: Variable: 86
                                                                      └──Desc: Variable: y
                                                                   └──Pattern:
                                                                      └──Type expr: Mu
                                                                         └──Variable: 87
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 86
                                                                                     └──Type expr: Variable: 87
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row uniform
                                                                                     └──Type expr: Constructor: absent
                                                                      └──Desc: Variable: t3
                                                             └──Abstraction:
                                                                └──Variables:
                                                                └──Expression:
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 86
                                                                      └──Type expr: Mu
                                                                         └──Variable: 87
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 86
                                                                                     └──Type expr: Variable: 87
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row uniform
                                                                                     └──Type expr: Constructor: absent
                                                                   └──Desc: Application
                                                                      └──Expression:
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Variable: 86
                                                                               └──Type expr: Constructor: bool
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 86
                                                                               └──Type expr: Mu
                                                                                  └──Variable: 87
                                                                                  └──Type expr: Variant
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Cons
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: 86
                                                                                              └──Type expr: Variable: 87
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Nil
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Constructor: unit
                                                                                           └──Type expr: Row uniform
                                                                                              └──Type expr: Constructor: absent
                                                                         └──Desc: Application
                                                                            └──Expression:
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Mu
                                                                                     └──Variable: 87
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: 86
                                                                                                 └──Type expr: Variable: 87
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Nil
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Constructor: unit
                                                                                              └──Type expr: Row uniform
                                                                                                 └──Type expr: Constructor: absent
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Variable: 86
                                                                                        └──Type expr: Constructor: bool
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Variable: 86
                                                                                        └──Type expr: Mu
                                                                                           └──Variable: 87
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: 86
                                                                                                       └──Type expr: Variable: 87
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Nil
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Constructor: unit
                                                                                                    └──Type expr: Row uniform
                                                                                                       └──Type expr: Constructor: absent
                                                                               └──Desc: Variable
                                                                                  └──Variable: select
                                                                            └──Expression:
                                                                               └──Type expr: Mu
                                                                                  └──Variable: 87
                                                                                  └──Type expr: Variant
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Cons
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: 86
                                                                                              └──Type expr: Variable: 87
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Nil
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Constructor: unit
                                                                                           └──Type expr: Row uniform
                                                                                              └──Type expr: Constructor: absent
                                                                               └──Desc: Variable
                                                                                  └──Variable: t2
                                                                      └──Expression:
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Variable: 86
                                                                            └──Type expr: Constructor: bool
                                                                         └──Desc: Variable
                                                                            └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 86
                                                             └──Type expr: Mu
                                                                └──Variable: 87
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 86
                                                                            └──Type expr: Variable: 87
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Variable: 86
                                                                └──Desc: Variable
                                                                   └──Variable: y
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: 87
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 86
                                                                               └──Type expr: Variable: 87
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row uniform
                                                                               └──Type expr: Constructor: absent
                                                                └──Desc: Variant
                                                                   └──Variant description:
                                                                      └──Tag: Cons
                                                                      └──Variant row:
                                                                         └──Type expr: Mu
                                                                            └──Variable: 26
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 86
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Variable: 26
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row uniform
                                                                                     └──Type expr: Constructor: absent
                                                                   └──Expression:
                                                                      └──Type expr: Mu
                                                                         └──Variable: 19
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 86
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cons
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Variable: 19
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Nil
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Row uniform
                                                                                        └──Type expr: Constructor: absent
                                                                      └──Desc: Tuple
                                                                         └──Expression:
                                                                            └──Type expr: Variable: 86
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Mu
                                                                               └──Variable: 87
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: 86
                                                                                           └──Type expr: Variable: 87
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Nil
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Row uniform
                                                                                           └──Type expr: Constructor: absent
                                                                            └──Desc: Variable
                                                                               └──Variable: t3
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: fold_right
                └──Abstraction:
                   └──Variables: 145,148
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Mu
                            └──Variable: 157
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Nil
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 148
                                           └──Type expr: Variable: 157
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Arrow
                            └──Type expr: Variable: 145
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 148
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 145
                                     └──Type expr: Variable: 145
                               └──Type expr: Variable: 145
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Mu
                               └──Variable: 157
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 148
                                              └──Type expr: Variable: 157
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: 145
                               └──Type expr: Arrow
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 148
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: 145
                                        └──Type expr: Variable: 145
                                  └──Type expr: Variable: 145
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: 145
                                  └──Desc: Variable: init
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: 148
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: 145
                                           └──Type expr: Variable: 145
                                     └──Type expr: Variable: 145
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: 148
                                           └──Type expr: Arrow
                                              └──Type expr: Variable: 145
                                              └──Type expr: Variable: 145
                                        └──Desc: Variable: f
                                     └──Expression:
                                        └──Type expr: Variable: 145
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Mu
                                                 └──Variable: 157
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Nil
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 148
                                                                └──Type expr: Variable: 157
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                              └──Desc: Variable
                                                 └──Variable: t
                                           └──Type expr: Mu
                                              └──Variable: 157
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Nil
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 148
                                                             └──Type expr: Variable: 157
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                           └──Cases:
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Mu
                                                                   └──Variable: 117
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 148
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Variable: 117
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                                    └──Desc: Variant
                                                       └──Variant description:
                                                          └──Tag: Nil
                                                          └──Variant row:
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Mu
                                                                         └──Variable: 117
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 148
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Variable: 117
                                                                                     └──Type expr: Row uniform
                                                                                        └──Type expr: Constructor: absent
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                 └──Expression:
                                                    └──Type expr: Variable: 145
                                                    └──Desc: Variable
                                                       └──Variable: init
                                              └──Case:
                                                 └──Pattern:
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Mu
                                                                   └──Variable: 117
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 148
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Variable: 117
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                                    └──Desc: Variant
                                                       └──Variant description:
                                                          └──Tag: Cons
                                                          └──Variant row:
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Mu
                                                                         └──Variable: 117
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 148
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Variable: 117
                                                                                     └──Type expr: Row uniform
                                                                                        └──Type expr: Constructor: absent
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                       └──Pattern:
                                                          └──Type expr: Mu
                                                             └──Variable: 117
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 148
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Variable: 117
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Variable: 148
                                                                └──Desc: Variable: x
                                                             └──Pattern:
                                                                └──Type expr: Mu
                                                                   └──Variable: 157
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: 148
                                                                                  └──Type expr: Variable: 157
                                                                            └──Type expr: Row uniform
                                                                               └──Type expr: Constructor: absent
                                                                └──Desc: Variable: t
                                                 └──Expression:
                                                    └──Type expr: Variable: 145
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 145
                                                             └──Type expr: Variable: 145
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: 148
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: 145
                                                                      └──Type expr: Variable: 145
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Variable: 148
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Variable: 145
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: 148
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: 145
                                                                         └──Type expr: Variable: 145
                                                                   └──Type expr: Variable: 145
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: 145
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Variable: 148
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: 145
                                                                                  └──Type expr: Variable: 145
                                                                            └──Type expr: Variable: 145
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Mu
                                                                                  └──Variable: 157
                                                                                  └──Type expr: Variant
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Nil
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: 148
                                                                                                 └──Type expr: Variable: 157
                                                                                           └──Type expr: Row uniform
                                                                                              └──Type expr: Constructor: absent
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: 145
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Variable: 148
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Variable: 145
                                                                                           └──Type expr: Variable: 145
                                                                                     └──Type expr: Variable: 145
                                                                            └──Desc: Variable
                                                                               └──Variable: fold_right
                                                                         └──Expression:
                                                                            └──Type expr: Mu
                                                                               └──Variable: 157
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Nil
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Cons
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: 148
                                                                                              └──Type expr: Variable: 157
                                                                                        └──Type expr: Row uniform
                                                                                           └──Type expr: Constructor: absent
                                                                            └──Desc: Variable
                                                                               └──Variable: t
                                                                   └──Expression:
                                                                      └──Type expr: Variable: 145
                                                                      └──Desc: Variable
                                                                         └──Variable: init
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: 148
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: 145
                                                                      └──Type expr: Variable: 145
                                                                └──Desc: Variable
                                                                   └──Variable: f
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Mu
                         └──Variable: 179
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Nil
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: 272
                                        └──Type expr: Variable: 179
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: 272
                            └──Type expr: Constructor: bool
                         └──Type expr: Tuple
                            └──Type expr: Mu
                               └──Variable: 253
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 272
                                           └──Type expr: Variable: 253
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Variable: 258
                            └──Type expr: Mu
                               └──Variable: 273
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 272
                                           └──Type expr: Variable: 273
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Variable: 278
                   └──Desc: Variable: partition
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Mu
                            └──Variable: 179
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Nil
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 272
                                           └──Type expr: Variable: 179
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: 272
                               └──Type expr: Constructor: bool
                            └──Type expr: Tuple
                               └──Type expr: Mu
                                  └──Variable: 253
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 272
                                              └──Type expr: Variable: 253
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: 258
                               └──Type expr: Mu
                                  └──Variable: 273
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 272
                                              └──Type expr: Variable: 273
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: 278
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Mu
                               └──Variable: 179
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 272
                                              └──Type expr: Variable: 179
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 272
                                  └──Type expr: Constructor: bool
                               └──Type expr: Tuple
                                  └──Type expr: Mu
                                     └──Variable: 253
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: 272
                                                 └──Type expr: Variable: 253
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: 258
                                  └──Type expr: Mu
                                     └──Variable: 273
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: 272
                                                 └──Type expr: Variable: 273
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: 278
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 272
                                     └──Type expr: Constructor: bool
                                  └──Desc: Variable: f
                               └──Expression:
                                  └──Type expr: Tuple
                                     └──Type expr: Mu
                                        └──Variable: 253
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 272
                                                    └──Type expr: Variable: 253
                                              └──Type expr: Row cons
                                                 └──Label: Nil
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Variable: 258
                                     └──Type expr: Mu
                                        └──Variable: 273
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 272
                                                    └──Type expr: Variable: 273
                                              └──Type expr: Row cons
                                                 └──Label: Nil
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Variable: 278
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Variable: 272
                                              └──Type expr: Arrow
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: 253
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 272
                                                                   └──Type expr: Variable: 253
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 258
                                                    └──Type expr: Mu
                                                       └──Variable: 273
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 272
                                                                   └──Type expr: Variable: 273
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 278
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: 253
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 272
                                                                   └──Type expr: Variable: 253
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 258
                                                    └──Type expr: Mu
                                                       └──Variable: 273
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 272
                                                                   └──Type expr: Variable: 273
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 278
                                           └──Type expr: Tuple
                                              └──Type expr: Mu
                                                 └──Variable: 253
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 272
                                                             └──Type expr: Variable: 253
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: 258
                                              └──Type expr: Mu
                                                 └──Variable: 273
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 272
                                                             └──Type expr: Variable: 273
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: 278
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: 253
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 272
                                                                   └──Type expr: Variable: 253
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 258
                                                    └──Type expr: Mu
                                                       └──Variable: 273
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 272
                                                                   └──Type expr: Variable: 273
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 278
                                                 └──Type expr: Arrow
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 272
                                                       └──Type expr: Arrow
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: 253
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 272
                                                                            └──Type expr: Variable: 253
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 258
                                                             └──Type expr: Mu
                                                                └──Variable: 273
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 272
                                                                            └──Type expr: Variable: 273
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 278
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: 253
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 272
                                                                            └──Type expr: Variable: 253
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 258
                                                             └──Type expr: Mu
                                                                └──Variable: 273
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 272
                                                                            └──Type expr: Variable: 273
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 278
                                                    └──Type expr: Tuple
                                                       └──Type expr: Mu
                                                          └──Variable: 253
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 272
                                                                      └──Type expr: Variable: 253
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: 258
                                                       └──Type expr: Mu
                                                          └──Variable: 273
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 272
                                                                      └──Type expr: Variable: 273
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: 278
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Mu
                                                          └──Variable: 179
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 272
                                                                         └──Type expr: Variable: 179
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                       └──Type expr: Arrow
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: 253
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 272
                                                                            └──Type expr: Variable: 253
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 258
                                                             └──Type expr: Mu
                                                                └──Variable: 273
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 272
                                                                            └──Type expr: Variable: 273
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 278
                                                          └──Type expr: Arrow
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: 272
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Mu
                                                                         └──Variable: 253
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 272
                                                                                     └──Type expr: Variable: 253
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: 258
                                                                      └──Type expr: Mu
                                                                         └──Variable: 273
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 272
                                                                                     └──Type expr: Variable: 273
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: 278
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Mu
                                                                         └──Variable: 253
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 272
                                                                                     └──Type expr: Variable: 253
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: 258
                                                                      └──Type expr: Mu
                                                                         └──Variable: 273
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 272
                                                                                     └──Type expr: Variable: 273
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: 278
                                                             └──Type expr: Tuple
                                                                └──Type expr: Mu
                                                                   └──Variable: 253
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 272
                                                                               └──Type expr: Variable: 253
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: 258
                                                                └──Type expr: Mu
                                                                   └──Variable: 273
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 272
                                                                               └──Type expr: Variable: 273
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: 278
                                                    └──Desc: Variable
                                                       └──Variable: fold_right
                                                       └──Type expr: Tuple
                                                          └──Type expr: Mu
                                                             └──Variable: 253
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 272
                                                                         └──Type expr: Variable: 253
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: 258
                                                          └──Type expr: Mu
                                                             └──Variable: 273
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 272
                                                                         └──Type expr: Variable: 273
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: 278
                                                       └──Type expr: Variable: 272
                                                 └──Expression:
                                                    └──Type expr: Mu
                                                       └──Variable: 179
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 272
                                                                      └──Type expr: Variable: 179
                                                                └──Type expr: Row uniform
                                                                   └──Type expr: Constructor: absent
                                                    └──Desc: Variable
                                                       └──Variable: t
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Mu
                                                    └──Variable: 253
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 272
                                                                └──Type expr: Variable: 253
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: 258
                                                 └──Type expr: Mu
                                                    └──Variable: 273
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 272
                                                                └──Type expr: Variable: 273
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: 278
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Mu
                                                       └──Variable: 253
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 272
                                                                   └──Type expr: Variable: 253
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 258
                                                    └──Desc: Variant
                                                       └──Variant description:
                                                          └──Tag: Nil
                                                          └──Variant row:
                                                             └──Type expr: Mu
                                                                └──Variable: 202
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 272
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Variable: 202
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: 258
                                                 └──Expression:
                                                    └──Type expr: Mu
                                                       └──Variable: 273
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 272
                                                                   └──Type expr: Variable: 273
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 278
                                                    └──Desc: Variant
                                                       └──Variant description:
                                                          └──Tag: Nil
                                                          └──Variant row:
                                                             └──Type expr: Mu
                                                                └──Variable: 213
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 272
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Variable: 213
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: 278
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: 272
                                           └──Type expr: Arrow
                                              └──Type expr: Tuple
                                                 └──Type expr: Mu
                                                    └──Variable: 253
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 272
                                                                └──Type expr: Variable: 253
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: 258
                                                 └──Type expr: Mu
                                                    └──Variable: 273
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 272
                                                                └──Type expr: Variable: 273
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: 278
                                              └──Type expr: Tuple
                                                 └──Type expr: Mu
                                                    └──Variable: 253
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 272
                                                                └──Type expr: Variable: 253
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: 258
                                                 └──Type expr: Mu
                                                    └──Variable: 273
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 272
                                                                └──Type expr: Variable: 273
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: 278
                                        └──Desc: Function
                                           └──Pattern:
                                              └──Type expr: Variable: 272
                                              └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: 253
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 272
                                                                   └──Type expr: Variable: 253
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 258
                                                    └──Type expr: Mu
                                                       └──Variable: 273
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 272
                                                                   └──Type expr: Variable: 273
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 278
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: 253
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 272
                                                                   └──Type expr: Variable: 253
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 258
                                                    └──Type expr: Mu
                                                       └──Variable: 273
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 272
                                                                   └──Type expr: Variable: 273
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 278
                                              └──Desc: Function
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Mu
                                                          └──Variable: 253
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 272
                                                                      └──Type expr: Variable: 253
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: 258
                                                       └──Type expr: Mu
                                                          └──Variable: 273
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 272
                                                                      └──Type expr: Variable: 273
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: 278
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Mu
                                                             └──Variable: 253
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 272
                                                                         └──Type expr: Variable: 253
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: 258
                                                          └──Desc: Variable: l
                                                       └──Pattern:
                                                          └──Type expr: Mu
                                                             └──Variable: 273
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 272
                                                                         └──Type expr: Variable: 273
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: 278
                                                          └──Desc: Variable: r
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Mu
                                                          └──Variable: 253
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 272
                                                                      └──Type expr: Variable: 253
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: 258
                                                       └──Type expr: Mu
                                                          └──Variable: 273
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 272
                                                                      └──Type expr: Variable: 273
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: 278
                                                    └──Desc: If
                                                       └──Expression:
                                                          └──Type expr: Constructor: bool
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: 272
                                                                   └──Type expr: Constructor: bool
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Variable: 272
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: 253
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 272
                                                                            └──Type expr: Variable: 253
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 258
                                                             └──Type expr: Mu
                                                                └──Variable: 273
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 272
                                                                            └──Type expr: Variable: 273
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 278
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: 253
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 272
                                                                               └──Type expr: Variable: 253
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: 258
                                                                └──Desc: Variant
                                                                   └──Variant description:
                                                                      └──Tag: Cons
                                                                      └──Variant row:
                                                                         └──Type expr: Mu
                                                                            └──Variable: 202
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 272
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Variable: 202
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: 258
                                                                   └──Expression:
                                                                      └──Type expr: Mu
                                                                         └──Variable: 247
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 272
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cons
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Variable: 247
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Nil
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Variable: 258
                                                                      └──Desc: Tuple
                                                                         └──Expression:
                                                                            └──Type expr: Variable: 272
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Mu
                                                                               └──Variable: 253
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: 272
                                                                                           └──Type expr: Variable: 253
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Nil
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Variable: 258
                                                                            └──Desc: Variable
                                                                               └──Variable: l
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: 273
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 272
                                                                               └──Type expr: Variable: 273
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: 278
                                                                └──Desc: Variable
                                                                   └──Variable: r
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: 253
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 272
                                                                            └──Type expr: Variable: 253
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 258
                                                             └──Type expr: Mu
                                                                └──Variable: 273
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 272
                                                                            └──Type expr: Variable: 273
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 278
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: 253
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 272
                                                                               └──Type expr: Variable: 253
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: 258
                                                                └──Desc: Variable
                                                                   └──Variable: l
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: 273
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 272
                                                                               └──Type expr: Variable: 273
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: 278
                                                                └──Desc: Variant
                                                                   └──Variant description:
                                                                      └──Tag: Cons
                                                                      └──Variant row:
                                                                         └──Type expr: Mu
                                                                            └──Variable: 213
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 272
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Variable: 213
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: 278
                                                                   └──Expression:
                                                                      └──Type expr: Mu
                                                                         └──Variable: 267
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 272
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cons
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Variable: 267
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Nil
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Variable: 278
                                                                      └──Desc: Tuple
                                                                         └──Expression:
                                                                            └──Type expr: Variable: 272
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Mu
                                                                               └──Variable: 273
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: 272
                                                                                           └──Type expr: Variable: 273
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Nil
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Variable: 278
                                                                            └──Desc: Variable
                                                                               └──Variable: r
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 283
                      └──Type expr: Variable: 283
                   └──Desc: Variable: id
                └──Abstraction:
                   └──Variables: 283,283
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 283
                         └──Type expr: Variable: 283
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 283
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: 283
                            └──Desc: Variable
                               └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: 299
                         └──Type expr: Variable: 296
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: 302
                            └──Type expr: Variable: 299
                         └──Type expr: Arrow
                            └──Type expr: Variable: 302
                            └──Type expr: Variable: 296
                   └──Desc: Variable: compose
                └──Abstraction:
                   └──Variables: 296
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: 299
                            └──Type expr: Variable: 296
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: 302
                               └──Type expr: Variable: 299
                            └──Type expr: Arrow
                               └──Type expr: Variable: 302
                               └──Type expr: Variable: 296
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Variable: 299
                               └──Type expr: Variable: 296
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 302
                                  └──Type expr: Variable: 299
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 302
                                  └──Type expr: Variable: 296
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 302
                                     └──Type expr: Variable: 299
                                  └──Desc: Variable: g
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 302
                                     └──Type expr: Variable: 296
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: 302
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: 296
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: 299
                                                 └──Type expr: Variable: 296
                                              └──Desc: Variable
                                                 └──Variable: f
                                           └──Expression:
                                              └──Type expr: Variable: 299
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 302
                                                       └──Type expr: Variable: 299
                                                    └──Desc: Variable
                                                       └──Variable: g
                                                 └──Expression:
                                                    └──Type expr: Variable: 302
                                                    └──Desc: Variable
                                                       └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 321
                      └──Type expr: Arrow
                         └──Type expr: Variable: 322
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Cons
                               └──Type expr: Constructor: present
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: 321
                                     └──Type expr: Variable: 322
                               └──Type expr: Variable: 315
                   └──Desc: Variable: cons
                └──Abstraction:
                   └──Variables: 321,321
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 321
                         └──Type expr: Arrow
                            └──Type expr: Variable: 322
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: 321
                                        └──Type expr: Variable: 322
                                  └──Type expr: Variable: 315
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 321
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: 322
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 321
                                           └──Type expr: Variable: 322
                                     └──Type expr: Variable: 315
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: 322
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 321
                                              └──Type expr: Variable: 322
                                        └──Type expr: Variable: 315
                                  └──Desc: Variant
                                     └──Variant description:
                                        └──Tag: Cons
                                        └──Variant row:
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 321
                                                    └──Type expr: Variable: 322
                                              └──Type expr: Variable: 315
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 321
                                           └──Type expr: Variable: 322
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Variable: 321
                                              └──Desc: Variable
                                                 └──Variable: x
                                           └──Expression:
                                              └──Type expr: Variable: 322
                                              └──Desc: Variable
                                                 └──Variable: t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: 491
                         └──Type expr: Constructor: bool
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: 491
                            └──Type expr: Arrow
                               └──Type expr: Variable: 491
                               └──Type expr: Constructor: bool
                         └──Type expr: Arrow
                            └──Type expr: Mu
                               └──Variable: 511
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 491
                                           └──Type expr: Variable: 511
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                            └──Type expr: Arrow
                               └──Type expr: Mu
                                  └──Variable: 521
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 491
                                              └──Type expr: Variable: 521
                                        └──Type expr: Variable: 523
                               └──Type expr: Mu
                                  └──Variable: 521
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 491
                                              └──Type expr: Variable: 521
                                        └──Type expr: Variable: 523
                   └──Desc: Variable: sort_append
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: 491
                            └──Type expr: Constructor: bool
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: 491
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 491
                                  └──Type expr: Constructor: bool
                            └──Type expr: Arrow
                               └──Type expr: Mu
                                  └──Variable: 511
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 491
                                              └──Type expr: Variable: 511
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                               └──Type expr: Arrow
                                  └──Type expr: Mu
                                     └──Variable: 521
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: 491
                                                 └──Type expr: Variable: 521
                                           └──Type expr: Variable: 523
                                  └──Type expr: Mu
                                     └──Variable: 521
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: 491
                                                 └──Type expr: Variable: 521
                                           └──Type expr: Variable: 523
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Variable: 491
                               └──Type expr: Constructor: bool
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 491
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 491
                                     └──Type expr: Constructor: bool
                               └──Type expr: Arrow
                                  └──Type expr: Mu
                                     └──Variable: 511
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: 491
                                                 └──Type expr: Variable: 511
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                                  └──Type expr: Arrow
                                     └──Type expr: Mu
                                        └──Variable: 521
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 491
                                                    └──Type expr: Variable: 521
                                              └──Type expr: Variable: 523
                                     └──Type expr: Mu
                                        └──Variable: 521
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 491
                                                    └──Type expr: Variable: 521
                                              └──Type expr: Variable: 523
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 491
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: 491
                                        └──Type expr: Constructor: bool
                                  └──Desc: Variable: le
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Mu
                                        └──Variable: 511
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 491
                                                    └──Type expr: Variable: 511
                                              └──Type expr: Row cons
                                                 └──Label: Nil
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                     └──Type expr: Arrow
                                        └──Type expr: Mu
                                           └──Variable: 521
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Cons
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 491
                                                       └──Type expr: Variable: 521
                                                 └──Type expr: Variable: 523
                                        └──Type expr: Mu
                                           └──Variable: 521
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Cons
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 491
                                                       └──Type expr: Variable: 521
                                                 └──Type expr: Variable: 523
                                  └──Desc: Let rec
                                     └──Value bindings:
                                        └──Value binding:
                                           └──Variable: loop
                                           └──Abstraction:
                                              └──Variables: 500
                                              └──Expression:
                                                 └──Type expr: Arrow
                                                    └──Type expr: Mu
                                                       └──Variable: 503
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 491
                                                                   └──Type expr: Variable: 503
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row uniform
                                                                   └──Type expr: Constructor: absent
                                                    └──Type expr: Arrow
                                                       └──Type expr: Mu
                                                          └──Variable: 485
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 491
                                                                      └──Type expr: Variable: 485
                                                                └──Type expr: Variable: 500
                                                       └──Type expr: Mu
                                                          └──Variable: 485
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 491
                                                                      └──Type expr: Variable: 485
                                                                └──Type expr: Variable: 500
                                                 └──Desc: Function
                                                    └──Pattern:
                                                       └──Type expr: Mu
                                                          └──Variable: 503
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 491
                                                                      └──Type expr: Variable: 503
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                       └──Desc: Variable: t
                                                    └──Expression:
                                                       └──Type expr: Arrow
                                                          └──Type expr: Mu
                                                             └──Variable: 485
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 491
                                                                         └──Type expr: Variable: 485
                                                                   └──Type expr: Variable: 500
                                                          └──Type expr: Mu
                                                             └──Variable: 485
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 491
                                                                         └──Type expr: Variable: 485
                                                                   └──Type expr: Variable: 500
                                                       └──Desc: Match
                                                          └──Expression:
                                                             └──Type expr: Mu
                                                                └──Variable: 503
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 491
                                                                            └──Type expr: Variable: 503
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                                             └──Desc: Variable
                                                                └──Variable: t
                                                          └──Type expr: Mu
                                                             └──Variable: 503
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 491
                                                                         └──Type expr: Variable: 503
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                          └──Cases:
                                                             └──Case:
                                                                └──Pattern:
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Mu
                                                                                  └──Variable: 423
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 491
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Variable: 423
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Nil
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Constructor: unit
                                                                                              └──Type expr: Row uniform
                                                                                                 └──Type expr: Constructor: absent
                                                                            └──Type expr: Row uniform
                                                                               └──Type expr: Constructor: absent
                                                                   └──Desc: Variant
                                                                      └──Variant description:
                                                                         └──Tag: Nil
                                                                         └──Variant row:
                                                                            └──Type expr: Row cons
                                                                               └──Label: Nil
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cons
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Mu
                                                                                        └──Variable: 423
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: 491
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Variable: 423
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Nil
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Constructor: unit
                                                                                                    └──Type expr: Row uniform
                                                                                                       └──Type expr: Constructor: absent
                                                                                  └──Type expr: Row uniform
                                                                                     └──Type expr: Constructor: absent
                                                                └──Expression:
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Mu
                                                                         └──Variable: 485
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 491
                                                                                     └──Type expr: Variable: 485
                                                                               └──Type expr: Variable: 500
                                                                      └──Type expr: Mu
                                                                         └──Variable: 485
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 491
                                                                                     └──Type expr: Variable: 485
                                                                               └──Type expr: Variable: 500
                                                                   └──Desc: Variable
                                                                      └──Variable: id
                                                                      └──Type expr: Mu
                                                                         └──Variable: 485
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 491
                                                                                     └──Type expr: Variable: 485
                                                                               └──Type expr: Variable: 500
                                                             └──Case:
                                                                └──Pattern:
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Mu
                                                                                  └──Variable: 423
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 491
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Variable: 423
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Nil
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Constructor: unit
                                                                                              └──Type expr: Row uniform
                                                                                                 └──Type expr: Constructor: absent
                                                                            └──Type expr: Row uniform
                                                                               └──Type expr: Constructor: absent
                                                                   └──Desc: Variant
                                                                      └──Variant description:
                                                                         └──Tag: Cons
                                                                         └──Variant row:
                                                                            └──Type expr: Row cons
                                                                               └──Label: Nil
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cons
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Mu
                                                                                        └──Variable: 423
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: 491
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Variable: 423
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Nil
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Constructor: unit
                                                                                                    └──Type expr: Row uniform
                                                                                                       └──Type expr: Constructor: absent
                                                                                  └──Type expr: Row uniform
                                                                                     └──Type expr: Constructor: absent
                                                                      └──Pattern:
                                                                         └──Type expr: Mu
                                                                            └──Variable: 423
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 491
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Variable: 423
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Nil
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Row uniform
                                                                                           └──Type expr: Constructor: absent
                                                                         └──Desc: Tuple
                                                                            └──Pattern:
                                                                               └──Type expr: Variable: 491
                                                                               └──Desc: Any
                                                                            └──Pattern:
                                                                               └──Type expr: Mu
                                                                                  └──Variable: 503
                                                                                  └──Type expr: Variant
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Cons
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: 491
                                                                                              └──Type expr: Variable: 503
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Nil
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Constructor: unit
                                                                                           └──Type expr: Row uniform
                                                                                              └──Type expr: Constructor: absent
                                                                               └──Desc: Any
                                                                └──Expression:
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Mu
                                                                         └──Variable: 485
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 491
                                                                                     └──Type expr: Variable: 485
                                                                               └──Type expr: Variable: 500
                                                                      └──Type expr: Mu
                                                                         └──Variable: 485
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 491
                                                                                     └──Type expr: Variable: 485
                                                                               └──Type expr: Variable: 500
                                                                   └──Desc: Let
                                                                      └──Value bindings:
                                                                         └──Value binding:
                                                                            └──Pattern:
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: 491
                                                                                  └──Type expr: Mu
                                                                                     └──Variable: 503
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: 491
                                                                                                 └──Type expr: Variable: 503
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Nil
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Constructor: unit
                                                                                              └──Type expr: Row uniform
                                                                                                 └──Type expr: Constructor: absent
                                                                               └──Desc: Tuple
                                                                                  └──Pattern:
                                                                                     └──Type expr: Variable: 491
                                                                                     └──Desc: Variable: pivot
                                                                                  └──Pattern:
                                                                                     └──Type expr: Mu
                                                                                        └──Variable: 503
                                                                                        └──Type expr: Variant
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Cons
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Tuple
                                                                                                    └──Type expr: Variable: 491
                                                                                                    └──Type expr: Variable: 503
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Nil
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Constructor: unit
                                                                                                 └──Type expr: Row uniform
                                                                                                    └──Type expr: Constructor: absent
                                                                                     └──Desc: Variable: t
                                                                            └──Abstraction:
                                                                               └──Variables:
                                                                               └──Expression:
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 491
                                                                                     └──Type expr: Mu
                                                                                        └──Variable: 503
                                                                                        └──Type expr: Variant
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Cons
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Tuple
                                                                                                    └──Type expr: Variable: 491
                                                                                                    └──Type expr: Variable: 503
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Nil
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Constructor: unit
                                                                                                 └──Type expr: Row uniform
                                                                                                    └──Type expr: Constructor: absent
                                                                                  └──Desc: Application
                                                                                     └──Expression:
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Variable: 491
                                                                                              └──Type expr: Constructor: bool
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: 491
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: 503
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: 491
                                                                                                             └──Type expr: Variable: 503
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Nil
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Constructor: unit
                                                                                                          └──Type expr: Row uniform
                                                                                                             └──Type expr: Constructor: absent
                                                                                        └──Desc: Application
                                                                                           └──Expression:
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: 503
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: 491
                                                                                                                └──Type expr: Variable: 503
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Nil
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Constructor: unit
                                                                                                             └──Type expr: Row uniform
                                                                                                                └──Type expr: Constructor: absent
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Variable: 491
                                                                                                       └──Type expr: Constructor: bool
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: 491
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: 503
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: 491
                                                                                                                      └──Type expr: Variable: 503
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Nil
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Constructor: unit
                                                                                                                   └──Type expr: Row uniform
                                                                                                                      └──Type expr: Constructor: absent
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: select
                                                                                                 └──Type expr: Variable: 491
                                                                                           └──Expression:
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: 503
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: 491
                                                                                                             └──Type expr: Variable: 503
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Nil
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Constructor: unit
                                                                                                          └──Type expr: Row uniform
                                                                                                             └──Type expr: Constructor: absent
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: t
                                                                                     └──Expression:
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Variable: 491
                                                                                           └──Type expr: Constructor: bool
                                                                                        └──Desc: Variable
                                                                                           └──Variable: f
                                                                      └──Expression:
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Mu
                                                                               └──Variable: 485
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: 491
                                                                                           └──Type expr: Variable: 485
                                                                                     └──Type expr: Variable: 500
                                                                            └──Type expr: Mu
                                                                               └──Variable: 485
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: 491
                                                                                           └──Type expr: Variable: 485
                                                                                     └──Type expr: Variable: 500
                                                                         └──Desc: Let
                                                                            └──Value bindings:
                                                                               └──Value binding:
                                                                                  └──Pattern:
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Mu
                                                                                           └──Variable: 503
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: 491
                                                                                                       └──Type expr: Variable: 503
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Nil
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Constructor: unit
                                                                                                    └──Type expr: Row uniform
                                                                                                       └──Type expr: Constructor: absent
                                                                                        └──Type expr: Mu
                                                                                           └──Variable: 503
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: 491
                                                                                                       └──Type expr: Variable: 503
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Nil
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Constructor: unit
                                                                                                    └──Type expr: Row uniform
                                                                                                       └──Type expr: Constructor: absent
                                                                                     └──Desc: Tuple
                                                                                        └──Pattern:
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: 503
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: 491
                                                                                                          └──Type expr: Variable: 503
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Nil
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Constructor: unit
                                                                                                       └──Type expr: Row uniform
                                                                                                          └──Type expr: Constructor: absent
                                                                                           └──Desc: Variable: l
                                                                                        └──Pattern:
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: 503
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: 491
                                                                                                          └──Type expr: Variable: 503
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Nil
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Constructor: unit
                                                                                                       └──Type expr: Row uniform
                                                                                                          └──Type expr: Constructor: absent
                                                                                           └──Desc: Variable: r
                                                                                  └──Abstraction:
                                                                                     └──Variables:
                                                                                     └──Expression:
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: 503
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: 491
                                                                                                          └──Type expr: Variable: 503
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Nil
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Constructor: unit
                                                                                                       └──Type expr: Row uniform
                                                                                                          └──Type expr: Constructor: absent
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: 503
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: 491
                                                                                                          └──Type expr: Variable: 503
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Nil
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Constructor: unit
                                                                                                       └──Type expr: Row uniform
                                                                                                          └──Type expr: Constructor: absent
                                                                                        └──Desc: Application
                                                                                           └──Expression:
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Variable: 491
                                                                                                    └──Type expr: Constructor: bool
                                                                                                 └──Type expr: Tuple
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 503
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 491
                                                                                                                   └──Type expr: Variable: 503
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Nil
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Constructor: unit
                                                                                                                └──Type expr: Row uniform
                                                                                                                   └──Type expr: Constructor: absent
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 503
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 491
                                                                                                                   └──Type expr: Variable: 503
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Nil
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Constructor: unit
                                                                                                                └──Type expr: Row uniform
                                                                                                                   └──Type expr: Constructor: absent
                                                                                              └──Desc: Application
                                                                                                 └──Expression:
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: 503
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: 491
                                                                                                                      └──Type expr: Variable: 503
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Nil
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Constructor: unit
                                                                                                                   └──Type expr: Row uniform
                                                                                                                      └──Type expr: Constructor: absent
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Arrow
                                                                                                             └──Type expr: Variable: 491
                                                                                                             └──Type expr: Constructor: bool
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Mu
                                                                                                                └──Variable: 503
                                                                                                                └──Type expr: Variant
                                                                                                                   └──Type expr: Row cons
                                                                                                                      └──Label: Cons
                                                                                                                      └──Type expr: Constructor: present
                                                                                                                         └──Type expr: Tuple
                                                                                                                            └──Type expr: Variable: 491
                                                                                                                            └──Type expr: Variable: 503
                                                                                                                      └──Type expr: Row cons
                                                                                                                         └──Label: Nil
                                                                                                                         └──Type expr: Constructor: present
                                                                                                                            └──Type expr: Constructor: unit
                                                                                                                         └──Type expr: Row uniform
                                                                                                                            └──Type expr: Constructor: absent
                                                                                                             └──Type expr: Mu
                                                                                                                └──Variable: 503
                                                                                                                └──Type expr: Variant
                                                                                                                   └──Type expr: Row cons
                                                                                                                      └──Label: Cons
                                                                                                                      └──Type expr: Constructor: present
                                                                                                                         └──Type expr: Tuple
                                                                                                                            └──Type expr: Variable: 491
                                                                                                                            └──Type expr: Variable: 503
                                                                                                                      └──Type expr: Row cons
                                                                                                                         └──Label: Nil
                                                                                                                         └──Type expr: Constructor: present
                                                                                                                            └──Type expr: Constructor: unit
                                                                                                                         └──Type expr: Row uniform
                                                                                                                            └──Type expr: Constructor: absent
                                                                                                    └──Desc: Variable
                                                                                                       └──Variable: partition
                                                                                                 └──Expression:
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 503
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 491
                                                                                                                   └──Type expr: Variable: 503
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Nil
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Constructor: unit
                                                                                                                └──Type expr: Row uniform
                                                                                                                   └──Type expr: Constructor: absent
                                                                                                    └──Desc: Variable
                                                                                                       └──Variable: t
                                                                                           └──Expression:
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Variable: 491
                                                                                                 └──Type expr: Constructor: bool
                                                                                              └──Desc: Function
                                                                                                 └──Pattern:
                                                                                                    └──Type expr: Variable: 491
                                                                                                    └──Desc: Variable: y
                                                                                                 └──Expression:
                                                                                                    └──Type expr: Constructor: bool
                                                                                                    └──Desc: Application
                                                                                                       └──Expression:
                                                                                                          └──Type expr: Arrow
                                                                                                             └──Type expr: Variable: 491
                                                                                                             └──Type expr: Constructor: bool
                                                                                                          └──Desc: Application
                                                                                                             └──Expression:
                                                                                                                └──Type expr: Arrow
                                                                                                                   └──Type expr: Variable: 491
                                                                                                                   └──Type expr: Arrow
                                                                                                                      └──Type expr: Variable: 491
                                                                                                                      └──Type expr: Constructor: bool
                                                                                                                └──Desc: Variable
                                                                                                                   └──Variable: le
                                                                                                             └──Expression:
                                                                                                                └──Type expr: Variable: 491
                                                                                                                └──Desc: Variable
                                                                                                                   └──Variable: y
                                                                                                       └──Expression:
                                                                                                          └──Type expr: Variable: 491
                                                                                                          └──Desc: Variable
                                                                                                             └──Variable: pivot
                                                                            └──Expression:
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Mu
                                                                                     └──Variable: 485
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: 491
                                                                                                 └──Type expr: Variable: 485
                                                                                           └──Type expr: Variable: 500
                                                                                  └──Type expr: Mu
                                                                                     └──Variable: 485
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: 491
                                                                                                 └──Type expr: Variable: 485
                                                                                           └──Type expr: Variable: 500
                                                                               └──Desc: Application
                                                                                  └──Expression:
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: 485
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: 491
                                                                                                          └──Type expr: Variable: 485
                                                                                                    └──Type expr: Variable: 500
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: 485
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: 491
                                                                                                          └──Type expr: Variable: 485
                                                                                                    └──Type expr: Variable: 500
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: 485
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: 491
                                                                                                          └──Type expr: Variable: 485
                                                                                                    └──Type expr: Variable: 500
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: 485
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: 491
                                                                                                          └──Type expr: Variable: 485
                                                                                                    └──Type expr: Variable: 500
                                                                                     └──Desc: Application
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: 485
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: 491
                                                                                                                └──Type expr: Variable: 485
                                                                                                          └──Type expr: Variable: 500
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: 485
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: 491
                                                                                                                └──Type expr: Variable: 485
                                                                                                          └──Type expr: Variable: 500
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 485
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 491
                                                                                                                   └──Type expr: Variable: 485
                                                                                                             └──Type expr: Variable: 500
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 485
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 491
                                                                                                                   └──Type expr: Variable: 485
                                                                                                             └──Type expr: Variable: 500
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 485
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 491
                                                                                                                   └──Type expr: Variable: 485
                                                                                                             └──Type expr: Variable: 500
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 485
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 491
                                                                                                                   └──Type expr: Variable: 485
                                                                                                             └──Type expr: Variable: 500
                                                                                           └──Desc: Variable
                                                                                              └──Variable: compose
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: 485
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: 491
                                                                                                             └──Type expr: Variable: 485
                                                                                                       └──Type expr: Variable: 500
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: 485
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: 491
                                                                                                             └──Type expr: Variable: 485
                                                                                                       └──Type expr: Variable: 500
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: 485
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: 491
                                                                                                             └──Type expr: Variable: 485
                                                                                                       └──Type expr: Variable: 500
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: 485
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: 491
                                                                                                             └──Type expr: Variable: 485
                                                                                                       └──Type expr: Variable: 500
                                                                                           └──Desc: Application
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 503
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 491
                                                                                                                   └──Type expr: Variable: 503
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Nil
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Constructor: unit
                                                                                                                └──Type expr: Row uniform
                                                                                                                   └──Type expr: Constructor: absent
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: 485
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: 491
                                                                                                                      └──Type expr: Variable: 485
                                                                                                                └──Type expr: Variable: 500
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: 485
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: 491
                                                                                                                      └──Type expr: Variable: 485
                                                                                                                └──Type expr: Variable: 500
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: loop
                                                                                              └──Expression:
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: 503
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: 491
                                                                                                                └──Type expr: Variable: 503
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Nil
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Constructor: unit
                                                                                                             └──Type expr: Row uniform
                                                                                                                └──Type expr: Constructor: absent
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: l
                                                                                  └──Expression:
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Mu
                                                                                           └──Variable: 485
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: 491
                                                                                                       └──Type expr: Variable: 485
                                                                                                 └──Type expr: Variable: 500
                                                                                        └──Type expr: Mu
                                                                                           └──Variable: 485
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: 491
                                                                                                       └──Type expr: Variable: 485
                                                                                                 └──Type expr: Variable: 500
                                                                                     └──Desc: Application
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: 485
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: 491
                                                                                                                └──Type expr: Variable: 485
                                                                                                          └──Type expr: Variable: 500
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: 485
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: 491
                                                                                                                └──Type expr: Variable: 485
                                                                                                          └──Type expr: Variable: 500
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: 485
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: 491
                                                                                                                └──Type expr: Variable: 485
                                                                                                          └──Type expr: Variable: 500
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: 485
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: 491
                                                                                                                └──Type expr: Variable: 485
                                                                                                          └──Type expr: Variable: 500
                                                                                           └──Desc: Application
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: 485
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: 491
                                                                                                                      └──Type expr: Variable: 485
                                                                                                                └──Type expr: Variable: 500
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: 485
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: 491
                                                                                                                      └──Type expr: Variable: 485
                                                                                                                └──Type expr: Variable: 500
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: 485
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: 491
                                                                                                                         └──Type expr: Variable: 485
                                                                                                                   └──Type expr: Variable: 500
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: 485
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: 491
                                                                                                                         └──Type expr: Variable: 485
                                                                                                                   └──Type expr: Variable: 500
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: 485
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: 491
                                                                                                                         └──Type expr: Variable: 485
                                                                                                                   └──Type expr: Variable: 500
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: 485
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: 491
                                                                                                                         └──Type expr: Variable: 485
                                                                                                                   └──Type expr: Variable: 500
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: compose
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 485
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 491
                                                                                                                   └──Type expr: Variable: 485
                                                                                                             └──Type expr: Variable: 500
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 485
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 491
                                                                                                                   └──Type expr: Variable: 485
                                                                                                             └──Type expr: Variable: 500
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 485
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 491
                                                                                                                   └──Type expr: Variable: 485
                                                                                                             └──Type expr: Variable: 500
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 485
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 491
                                                                                                                   └──Type expr: Variable: 485
                                                                                                             └──Type expr: Variable: 500
                                                                                                 └──Desc: Application
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Variable: 491
                                                                                                          └──Type expr: Arrow
                                                                                                             └──Type expr: Mu
                                                                                                                └──Variable: 485
                                                                                                                └──Type expr: Variant
                                                                                                                   └──Type expr: Row cons
                                                                                                                      └──Label: Cons
                                                                                                                      └──Type expr: Constructor: present
                                                                                                                         └──Type expr: Tuple
                                                                                                                            └──Type expr: Variable: 491
                                                                                                                            └──Type expr: Variable: 485
                                                                                                                      └──Type expr: Variable: 500
                                                                                                             └──Type expr: Mu
                                                                                                                └──Variable: 485
                                                                                                                └──Type expr: Variant
                                                                                                                   └──Type expr: Row cons
                                                                                                                      └──Label: Cons
                                                                                                                      └──Type expr: Constructor: present
                                                                                                                         └──Type expr: Tuple
                                                                                                                            └──Type expr: Variable: 491
                                                                                                                            └──Type expr: Variable: 485
                                                                                                                      └──Type expr: Variable: 500
                                                                                                       └──Desc: Variable
                                                                                                          └──Variable: cons
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: 485
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: 491
                                                                                                                         └──Type expr: Variable: 485
                                                                                                                   └──Type expr: Variable: 500
                                                                                                          └──Type expr: Variable: 491
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Variable: 491
                                                                                                       └──Desc: Variable
                                                                                                          └──Variable: pivot
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: 485
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: 491
                                                                                                             └──Type expr: Variable: 485
                                                                                                       └──Type expr: Variable: 500
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: 485
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: 491
                                                                                                             └──Type expr: Variable: 485
                                                                                                       └──Type expr: Variable: 500
                                                                                           └──Desc: Application
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 503
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 491
                                                                                                                   └──Type expr: Variable: 503
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Nil
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Constructor: unit
                                                                                                                └──Type expr: Row uniform
                                                                                                                   └──Type expr: Constructor: absent
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: 485
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: 491
                                                                                                                      └──Type expr: Variable: 485
                                                                                                                └──Type expr: Variable: 500
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: 485
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: 491
                                                                                                                      └──Type expr: Variable: 485
                                                                                                                └──Type expr: Variable: 500
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: loop
                                                                                              └──Expression:
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: 503
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: 491
                                                                                                                └──Type expr: Variable: 503
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Nil
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Constructor: unit
                                                                                                             └──Type expr: Row uniform
                                                                                                                └──Type expr: Constructor: absent
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: r
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Mu
                                              └──Variable: 511
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Cons
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 491
                                                          └──Type expr: Variable: 511
                                                    └──Type expr: Row cons
                                                       └──Label: Nil
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                           └──Type expr: Arrow
                                              └──Type expr: Mu
                                                 └──Variable: 521
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 491
                                                             └──Type expr: Variable: 521
                                                       └──Type expr: Variable: 523
                                              └──Type expr: Mu
                                                 └──Variable: 521
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 491
                                                             └──Type expr: Variable: 521
                                                       └──Type expr: Variable: 523
                                        └──Desc: Variable
                                           └──Variable: loop
                                           └──Type expr: Variable: 523
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Mu
                         └──Variable: 538
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Cons
                               └──Type expr: Constructor: present
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: 549
                                     └──Type expr: Variable: 538
                               └──Type expr: Row cons
                                  └──Label: Nil
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: 549
                            └──Type expr: Arrow
                               └──Type expr: Variable: 549
                               └──Type expr: Constructor: bool
                         └──Type expr: Mu
                            └──Variable: 532
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: 549
                                        └──Type expr: Variable: 532
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Variable: 588
                   └──Desc: Variable: sort
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Mu
                            └──Variable: 538
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: 549
                                        └──Type expr: Variable: 538
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: 549
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 549
                                  └──Type expr: Constructor: bool
                            └──Type expr: Mu
                               └──Variable: 532
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 549
                                           └──Type expr: Variable: 532
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Variable: 588
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Mu
                               └──Variable: 538
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 549
                                           └──Type expr: Variable: 538
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 549
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 549
                                     └──Type expr: Constructor: bool
                               └──Type expr: Mu
                                  └──Variable: 532
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 549
                                              └──Type expr: Variable: 532
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: 588
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 549
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: 549
                                        └──Type expr: Constructor: bool
                                  └──Desc: Variable: le
                               └──Expression:
                                  └──Type expr: Mu
                                     └──Variable: 532
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: 549
                                                 └──Type expr: Variable: 532
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: 588
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Mu
                                              └──Variable: 532
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Cons
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 549
                                                          └──Type expr: Variable: 532
                                                    └──Type expr: Row cons
                                                       └──Label: Nil
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: 588
                                           └──Type expr: Mu
                                              └──Variable: 532
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Cons
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 549
                                                          └──Type expr: Variable: 532
                                                    └──Type expr: Row cons
                                                       └──Label: Nil
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: 588
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Mu
                                                    └──Variable: 538
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 549
                                                                └──Type expr: Variable: 538
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                                 └──Type expr: Arrow
                                                    └──Type expr: Mu
                                                       └──Variable: 532
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 549
                                                                   └──Type expr: Variable: 532
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 588
                                                    └──Type expr: Mu
                                                       └──Variable: 532
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 549
                                                                   └──Type expr: Variable: 532
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 588
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: 549
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 549
                                                             └──Type expr: Constructor: bool
                                                       └──Type expr: Arrow
                                                          └──Type expr: Mu
                                                             └──Variable: 538
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 549
                                                                         └──Type expr: Variable: 538
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                          └──Type expr: Arrow
                                                             └──Type expr: Mu
                                                                └──Variable: 532
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 549
                                                                            └──Type expr: Variable: 532
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 588
                                                             └──Type expr: Mu
                                                                └──Variable: 532
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 549
                                                                            └──Type expr: Variable: 532
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 588
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: 549
                                                                └──Type expr: Constructor: bool
                                                             └──Type expr: Arrow
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: 549
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: 549
                                                                      └──Type expr: Constructor: bool
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Mu
                                                                      └──Variable: 538
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: 549
                                                                                  └──Type expr: Variable: 538
                                                                            └──Type expr: Row cons
                                                                               └──Label: Nil
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Mu
                                                                         └──Variable: 532
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 549
                                                                                     └──Type expr: Variable: 532
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: 588
                                                                      └──Type expr: Mu
                                                                         └──Variable: 532
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 549
                                                                                     └──Type expr: Variable: 532
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: 588
                                                          └──Desc: Variable
                                                             └──Variable: sort_append
                                                             └──Type expr: Variable: 549
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 549
                                                             └──Type expr: Constructor: bool
                                                          └──Desc: Function
                                                             └──Pattern:
                                                                └──Type expr: Variable: 549
                                                                └──Desc: Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: bool
                                                                └──Desc: Constant: true
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 549
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: 549
                                                          └──Type expr: Constructor: bool
                                                    └──Desc: Variable
                                                       └──Variable: le
                                           └──Expression:
                                              └──Type expr: Mu
                                                 └──Variable: 538
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 549
                                                             └──Type expr: Variable: 538
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                              └──Desc: Variable
                                                 └──Variable: t
                                     └──Expression:
                                        └──Type expr: Mu
                                           └──Variable: 532
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Cons
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 549
                                                       └──Type expr: Variable: 532
                                                 └──Type expr: Row cons
                                                    └──Label: Nil
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Variable: 588
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Nil
                                              └──Variant row:
                                                 └──Type expr: Mu
                                                    └──Variable: 567
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 549
                                                             └──Type expr: Variant
                                                                └──Type expr: Variable: 567
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: 588 |}]
