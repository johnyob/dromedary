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
  [%expect {|
    Structure:
    └──Structure:
       └──Structure item: Primitive
          └──Value description:
             └──Name: failwith
             └──Scheme:
                └──Variables: 12132
                └──Type expr: Arrow
                   └──Type expr: Constructor: string
                   └──Type expr: Variable: 12132
             └──Primitive name: %failwith
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: select
                └──Abstraction:
                   └──Variables: 12218
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Mu
                            └──Variable: 12219
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: 12218
                                        └──Type expr: Variable: 12219
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: 12218
                               └──Type expr: Constructor: bool
                            └──Type expr: Tuple
                               └──Type expr: Variable: 12218
                               └──Type expr: Mu
                                  └──Variable: 12219
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 12218
                                              └──Type expr: Variable: 12219
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Mu
                               └──Variable: 12219
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 12218
                                           └──Type expr: Variable: 12219
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
                                  └──Type expr: Variable: 12218
                                  └──Type expr: Constructor: bool
                               └──Type expr: Tuple
                                  └──Type expr: Variable: 12218
                                  └──Type expr: Mu
                                     └──Variable: 12219
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: 12218
                                                 └──Type expr: Variable: 12219
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 12218
                                     └──Type expr: Constructor: bool
                                  └──Desc: Variable: f
                               └──Expression:
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: 12218
                                     └──Type expr: Mu
                                        └──Variable: 12219
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 12218
                                                    └──Type expr: Variable: 12219
                                              └──Type expr: Row cons
                                                 └──Label: Nil
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Mu
                                           └──Variable: 12219
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Cons
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 12218
                                                       └──Type expr: Variable: 12219
                                                 └──Type expr: Row cons
                                                    └──Label: Nil
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                        └──Desc: Variable
                                           └──Variable: t1
                                     └──Type expr: Mu
                                        └──Variable: 12219
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 12218
                                                    └──Type expr: Variable: 12219
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
                                                             └──Variable: 12151
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 12218
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Variable: 12151
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
                                                                   └──Variable: 12151
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 12218
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Variable: 12151
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
                                                 └──Type expr: Variable: 12218
                                                 └──Type expr: Mu
                                                    └──Variable: 12219
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 12218
                                                                └──Type expr: Variable: 12219
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
                                                          └──Type expr: Variable: 12218
                                                          └──Type expr: Mu
                                                             └──Variable: 12219
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 12218
                                                                         └──Type expr: Variable: 12219
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                    └──Desc: Variable
                                                       └──Variable: failwith
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 12218
                                                          └──Type expr: Mu
                                                             └──Variable: 12219
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 12218
                                                                         └──Type expr: Variable: 12219
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
                                                             └──Variable: 12151
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 12218
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Variable: 12151
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
                                                                   └──Variable: 12151
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 12218
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Variable: 12151
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
                                                       └──Variable: 12151
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 12218
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Variable: 12151
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Variable: 12218
                                                          └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Mu
                                                             └──Variable: 12219
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 12218
                                                                         └──Type expr: Variable: 12219
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                          └──Desc: Variable: t2
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: 12218
                                                 └──Type expr: Mu
                                                    └──Variable: 12219
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 12218
                                                                └──Type expr: Variable: 12219
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
                                                             └──Type expr: Variable: 12218
                                                             └──Type expr: Constructor: bool
                                                          └──Desc: Variable
                                                             └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Variable: 12218
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 12218
                                                       └──Type expr: Mu
                                                          └──Variable: 12219
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 12218
                                                                      └──Type expr: Variable: 12219
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Variable: 12218
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Mu
                                                             └──Variable: 12219
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 12218
                                                                         └──Type expr: Variable: 12219
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
                                                       └──Type expr: Variable: 12218
                                                       └──Type expr: Mu
                                                          └──Variable: 12219
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 12218
                                                                      └──Type expr: Variable: 12219
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
                                                                   └──Type expr: Variable: 12218
                                                                   └──Type expr: Mu
                                                                      └──Variable: 12219
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: 12218
                                                                                  └──Type expr: Variable: 12219
                                                                            └──Type expr: Row cons
                                                                               └──Label: Nil
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                                                                └──Desc: Tuple
                                                                   └──Pattern:
                                                                      └──Type expr: Variable: 12218
                                                                      └──Desc: Variable: y
                                                                   └──Pattern:
                                                                      └──Type expr: Mu
                                                                         └──Variable: 12219
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 12218
                                                                                     └──Type expr: Variable: 12219
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
                                                                      └──Type expr: Variable: 12218
                                                                      └──Type expr: Mu
                                                                         └──Variable: 12219
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 12218
                                                                                     └──Type expr: Variable: 12219
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
                                                                               └──Type expr: Variable: 12218
                                                                               └──Type expr: Constructor: bool
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 12218
                                                                               └──Type expr: Mu
                                                                                  └──Variable: 12219
                                                                                  └──Type expr: Variant
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Cons
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: 12218
                                                                                              └──Type expr: Variable: 12219
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
                                                                                     └──Variable: 12219
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: 12218
                                                                                                 └──Type expr: Variable: 12219
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Nil
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Constructor: unit
                                                                                              └──Type expr: Row uniform
                                                                                                 └──Type expr: Constructor: absent
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Variable: 12218
                                                                                        └──Type expr: Constructor: bool
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Variable: 12218
                                                                                        └──Type expr: Mu
                                                                                           └──Variable: 12219
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: 12218
                                                                                                       └──Type expr: Variable: 12219
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
                                                                                  └──Variable: 12219
                                                                                  └──Type expr: Variant
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Cons
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: 12218
                                                                                              └──Type expr: Variable: 12219
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
                                                                            └──Type expr: Variable: 12218
                                                                            └──Type expr: Constructor: bool
                                                                         └──Desc: Variable
                                                                            └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 12218
                                                             └──Type expr: Mu
                                                                └──Variable: 12219
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 12218
                                                                            └──Type expr: Variable: 12219
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Variable: 12218
                                                                └──Desc: Variable
                                                                   └──Variable: y
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: 12219
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 12218
                                                                               └──Type expr: Variable: 12219
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
                                                                            └──Variable: 12158
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 12218
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Variable: 12158
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row uniform
                                                                                     └──Type expr: Constructor: absent
                                                                   └──Expression:
                                                                      └──Type expr: Mu
                                                                         └──Variable: 12151
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 12218
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cons
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Variable: 12151
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Nil
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Row uniform
                                                                                        └──Type expr: Constructor: absent
                                                                      └──Desc: Tuple
                                                                         └──Expression:
                                                                            └──Type expr: Variable: 12218
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Mu
                                                                               └──Variable: 12219
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: 12218
                                                                                           └──Type expr: Variable: 12219
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
                   └──Variables: 12277,12280
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Mu
                            └──Variable: 12289
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Nil
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 12280
                                           └──Type expr: Variable: 12289
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Arrow
                            └──Type expr: Variable: 12277
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 12280
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 12277
                                     └──Type expr: Variable: 12277
                               └──Type expr: Variable: 12277
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Mu
                               └──Variable: 12289
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 12280
                                              └──Type expr: Variable: 12289
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: 12277
                               └──Type expr: Arrow
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 12280
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: 12277
                                        └──Type expr: Variable: 12277
                                  └──Type expr: Variable: 12277
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: 12277
                                  └──Desc: Variable: init
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: 12280
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: 12277
                                           └──Type expr: Variable: 12277
                                     └──Type expr: Variable: 12277
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: 12280
                                           └──Type expr: Arrow
                                              └──Type expr: Variable: 12277
                                              └──Type expr: Variable: 12277
                                        └──Desc: Variable: f
                                     └──Expression:
                                        └──Type expr: Variable: 12277
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Mu
                                                 └──Variable: 12289
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Nil
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 12280
                                                                └──Type expr: Variable: 12289
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                              └──Desc: Variable
                                                 └──Variable: t
                                           └──Type expr: Mu
                                              └──Variable: 12289
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Nil
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 12280
                                                             └──Type expr: Variable: 12289
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
                                                                   └──Variable: 12249
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 12280
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Variable: 12249
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
                                                                         └──Variable: 12249
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 12280
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Variable: 12249
                                                                                     └──Type expr: Row uniform
                                                                                        └──Type expr: Constructor: absent
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                 └──Expression:
                                                    └──Type expr: Variable: 12277
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
                                                                   └──Variable: 12249
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 12280
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Variable: 12249
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
                                                                         └──Variable: 12249
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 12280
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Variable: 12249
                                                                                     └──Type expr: Row uniform
                                                                                        └──Type expr: Constructor: absent
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                       └──Pattern:
                                                          └──Type expr: Mu
                                                             └──Variable: 12249
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 12280
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Variable: 12249
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Variable: 12280
                                                                └──Desc: Variable: x
                                                             └──Pattern:
                                                                └──Type expr: Mu
                                                                   └──Variable: 12289
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: 12280
                                                                                  └──Type expr: Variable: 12289
                                                                            └──Type expr: Row uniform
                                                                               └──Type expr: Constructor: absent
                                                                └──Desc: Variable: t
                                                 └──Expression:
                                                    └──Type expr: Variable: 12277
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 12277
                                                             └──Type expr: Variable: 12277
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: 12280
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: 12277
                                                                      └──Type expr: Variable: 12277
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Variable: 12280
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Variable: 12277
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: 12280
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: 12277
                                                                         └──Type expr: Variable: 12277
                                                                   └──Type expr: Variable: 12277
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: 12277
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Variable: 12280
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: 12277
                                                                                  └──Type expr: Variable: 12277
                                                                            └──Type expr: Variable: 12277
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Mu
                                                                                  └──Variable: 12289
                                                                                  └──Type expr: Variant
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Nil
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: 12280
                                                                                                 └──Type expr: Variable: 12289
                                                                                           └──Type expr: Row uniform
                                                                                              └──Type expr: Constructor: absent
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: 12277
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Variable: 12280
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Variable: 12277
                                                                                           └──Type expr: Variable: 12277
                                                                                     └──Type expr: Variable: 12277
                                                                            └──Desc: Variable
                                                                               └──Variable: fold_right
                                                                         └──Expression:
                                                                            └──Type expr: Mu
                                                                               └──Variable: 12289
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Nil
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Cons
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: 12280
                                                                                              └──Type expr: Variable: 12289
                                                                                        └──Type expr: Row uniform
                                                                                           └──Type expr: Constructor: absent
                                                                            └──Desc: Variable
                                                                               └──Variable: t
                                                                   └──Expression:
                                                                      └──Type expr: Variable: 12277
                                                                      └──Desc: Variable
                                                                         └──Variable: init
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: 12280
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: 12277
                                                                      └──Type expr: Variable: 12277
                                                                └──Desc: Variable
                                                                   └──Variable: f
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Mu
                         └──Variable: 12311
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Nil
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: 12404
                                        └──Type expr: Variable: 12311
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: 12404
                            └──Type expr: Constructor: bool
                         └──Type expr: Tuple
                            └──Type expr: Mu
                               └──Variable: 12385
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 12404
                                           └──Type expr: Variable: 12385
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Variable: 12390
                            └──Type expr: Mu
                               └──Variable: 12405
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 12404
                                           └──Type expr: Variable: 12405
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Variable: 12410
                   └──Desc: Variable: partition
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Mu
                            └──Variable: 12311
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Nil
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 12404
                                           └──Type expr: Variable: 12311
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: 12404
                               └──Type expr: Constructor: bool
                            └──Type expr: Tuple
                               └──Type expr: Mu
                                  └──Variable: 12385
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 12404
                                              └──Type expr: Variable: 12385
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: 12390
                               └──Type expr: Mu
                                  └──Variable: 12405
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 12404
                                              └──Type expr: Variable: 12405
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: 12410
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Mu
                               └──Variable: 12311
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 12404
                                              └──Type expr: Variable: 12311
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 12404
                                  └──Type expr: Constructor: bool
                               └──Type expr: Tuple
                                  └──Type expr: Mu
                                     └──Variable: 12385
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: 12404
                                                 └──Type expr: Variable: 12385
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: 12390
                                  └──Type expr: Mu
                                     └──Variable: 12405
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: 12404
                                                 └──Type expr: Variable: 12405
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: 12410
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 12404
                                     └──Type expr: Constructor: bool
                                  └──Desc: Variable: f
                               └──Expression:
                                  └──Type expr: Tuple
                                     └──Type expr: Mu
                                        └──Variable: 12385
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 12404
                                                    └──Type expr: Variable: 12385
                                              └──Type expr: Row cons
                                                 └──Label: Nil
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Variable: 12390
                                     └──Type expr: Mu
                                        └──Variable: 12405
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 12404
                                                    └──Type expr: Variable: 12405
                                              └──Type expr: Row cons
                                                 └──Label: Nil
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Variable: 12410
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Variable: 12404
                                              └──Type expr: Arrow
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: 12385
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 12404
                                                                   └──Type expr: Variable: 12385
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 12390
                                                    └──Type expr: Mu
                                                       └──Variable: 12405
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 12404
                                                                   └──Type expr: Variable: 12405
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 12410
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: 12385
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 12404
                                                                   └──Type expr: Variable: 12385
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 12390
                                                    └──Type expr: Mu
                                                       └──Variable: 12405
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 12404
                                                                   └──Type expr: Variable: 12405
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 12410
                                           └──Type expr: Tuple
                                              └──Type expr: Mu
                                                 └──Variable: 12385
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 12404
                                                             └──Type expr: Variable: 12385
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: 12390
                                              └──Type expr: Mu
                                                 └──Variable: 12405
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 12404
                                                             └──Type expr: Variable: 12405
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: 12410
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: 12385
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 12404
                                                                   └──Type expr: Variable: 12385
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 12390
                                                    └──Type expr: Mu
                                                       └──Variable: 12405
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 12404
                                                                   └──Type expr: Variable: 12405
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 12410
                                                 └──Type expr: Arrow
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 12404
                                                       └──Type expr: Arrow
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: 12385
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 12404
                                                                            └──Type expr: Variable: 12385
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 12390
                                                             └──Type expr: Mu
                                                                └──Variable: 12405
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 12404
                                                                            └──Type expr: Variable: 12405
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 12410
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: 12385
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 12404
                                                                            └──Type expr: Variable: 12385
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 12390
                                                             └──Type expr: Mu
                                                                └──Variable: 12405
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 12404
                                                                            └──Type expr: Variable: 12405
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 12410
                                                    └──Type expr: Tuple
                                                       └──Type expr: Mu
                                                          └──Variable: 12385
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 12404
                                                                      └──Type expr: Variable: 12385
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: 12390
                                                       └──Type expr: Mu
                                                          └──Variable: 12405
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 12404
                                                                      └──Type expr: Variable: 12405
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: 12410
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Mu
                                                          └──Variable: 12311
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 12404
                                                                         └──Type expr: Variable: 12311
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                       └──Type expr: Arrow
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: 12385
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 12404
                                                                            └──Type expr: Variable: 12385
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 12390
                                                             └──Type expr: Mu
                                                                └──Variable: 12405
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 12404
                                                                            └──Type expr: Variable: 12405
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 12410
                                                          └──Type expr: Arrow
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: 12404
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Mu
                                                                         └──Variable: 12385
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 12404
                                                                                     └──Type expr: Variable: 12385
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: 12390
                                                                      └──Type expr: Mu
                                                                         └──Variable: 12405
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 12404
                                                                                     └──Type expr: Variable: 12405
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: 12410
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Mu
                                                                         └──Variable: 12385
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 12404
                                                                                     └──Type expr: Variable: 12385
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: 12390
                                                                      └──Type expr: Mu
                                                                         └──Variable: 12405
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 12404
                                                                                     └──Type expr: Variable: 12405
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: 12410
                                                             └──Type expr: Tuple
                                                                └──Type expr: Mu
                                                                   └──Variable: 12385
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 12404
                                                                               └──Type expr: Variable: 12385
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: 12390
                                                                └──Type expr: Mu
                                                                   └──Variable: 12405
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 12404
                                                                               └──Type expr: Variable: 12405
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: 12410
                                                    └──Desc: Variable
                                                       └──Variable: fold_right
                                                       └──Type expr: Tuple
                                                          └──Type expr: Mu
                                                             └──Variable: 12385
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 12404
                                                                         └──Type expr: Variable: 12385
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: 12390
                                                          └──Type expr: Mu
                                                             └──Variable: 12405
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 12404
                                                                         └──Type expr: Variable: 12405
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: 12410
                                                       └──Type expr: Variable: 12404
                                                 └──Expression:
                                                    └──Type expr: Mu
                                                       └──Variable: 12311
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 12404
                                                                      └──Type expr: Variable: 12311
                                                                └──Type expr: Row uniform
                                                                   └──Type expr: Constructor: absent
                                                    └──Desc: Variable
                                                       └──Variable: t
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Mu
                                                    └──Variable: 12385
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 12404
                                                                └──Type expr: Variable: 12385
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: 12390
                                                 └──Type expr: Mu
                                                    └──Variable: 12405
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 12404
                                                                └──Type expr: Variable: 12405
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: 12410
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Mu
                                                       └──Variable: 12385
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 12404
                                                                   └──Type expr: Variable: 12385
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 12390
                                                    └──Desc: Variant
                                                       └──Variant description:
                                                          └──Tag: Nil
                                                          └──Variant row:
                                                             └──Type expr: Mu
                                                                └──Variable: 12334
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 12404
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Variable: 12334
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: 12390
                                                 └──Expression:
                                                    └──Type expr: Mu
                                                       └──Variable: 12405
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 12404
                                                                   └──Type expr: Variable: 12405
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 12410
                                                    └──Desc: Variant
                                                       └──Variant description:
                                                          └──Tag: Nil
                                                          └──Variant row:
                                                             └──Type expr: Mu
                                                                └──Variable: 12345
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 12404
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Variable: 12345
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: 12410
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: 12404
                                           └──Type expr: Arrow
                                              └──Type expr: Tuple
                                                 └──Type expr: Mu
                                                    └──Variable: 12385
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 12404
                                                                └──Type expr: Variable: 12385
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: 12390
                                                 └──Type expr: Mu
                                                    └──Variable: 12405
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 12404
                                                                └──Type expr: Variable: 12405
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: 12410
                                              └──Type expr: Tuple
                                                 └──Type expr: Mu
                                                    └──Variable: 12385
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 12404
                                                                └──Type expr: Variable: 12385
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: 12390
                                                 └──Type expr: Mu
                                                    └──Variable: 12405
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 12404
                                                                └──Type expr: Variable: 12405
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: 12410
                                        └──Desc: Function
                                           └──Pattern:
                                              └──Type expr: Variable: 12404
                                              └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: 12385
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 12404
                                                                   └──Type expr: Variable: 12385
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 12390
                                                    └──Type expr: Mu
                                                       └──Variable: 12405
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 12404
                                                                   └──Type expr: Variable: 12405
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 12410
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: 12385
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 12404
                                                                   └──Type expr: Variable: 12385
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 12390
                                                    └──Type expr: Mu
                                                       └──Variable: 12405
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 12404
                                                                   └──Type expr: Variable: 12405
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 12410
                                              └──Desc: Function
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Mu
                                                          └──Variable: 12385
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 12404
                                                                      └──Type expr: Variable: 12385
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: 12390
                                                       └──Type expr: Mu
                                                          └──Variable: 12405
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 12404
                                                                      └──Type expr: Variable: 12405
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: 12410
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Mu
                                                             └──Variable: 12385
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 12404
                                                                         └──Type expr: Variable: 12385
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: 12390
                                                          └──Desc: Variable: l
                                                       └──Pattern:
                                                          └──Type expr: Mu
                                                             └──Variable: 12405
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 12404
                                                                         └──Type expr: Variable: 12405
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: 12410
                                                          └──Desc: Variable: r
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Mu
                                                          └──Variable: 12385
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 12404
                                                                      └──Type expr: Variable: 12385
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: 12390
                                                       └──Type expr: Mu
                                                          └──Variable: 12405
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 12404
                                                                      └──Type expr: Variable: 12405
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: 12410
                                                    └──Desc: If
                                                       └──Expression:
                                                          └──Type expr: Constructor: bool
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: 12404
                                                                   └──Type expr: Constructor: bool
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Variable: 12404
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: 12385
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 12404
                                                                            └──Type expr: Variable: 12385
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 12390
                                                             └──Type expr: Mu
                                                                └──Variable: 12405
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 12404
                                                                            └──Type expr: Variable: 12405
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 12410
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: 12385
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 12404
                                                                               └──Type expr: Variable: 12385
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: 12390
                                                                └──Desc: Variant
                                                                   └──Variant description:
                                                                      └──Tag: Cons
                                                                      └──Variant row:
                                                                         └──Type expr: Mu
                                                                            └──Variable: 12334
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 12404
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Variable: 12334
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: 12390
                                                                   └──Expression:
                                                                      └──Type expr: Mu
                                                                         └──Variable: 12379
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 12404
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cons
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Variable: 12379
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Nil
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Variable: 12390
                                                                      └──Desc: Tuple
                                                                         └──Expression:
                                                                            └──Type expr: Variable: 12404
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Mu
                                                                               └──Variable: 12385
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: 12404
                                                                                           └──Type expr: Variable: 12385
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Nil
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Variable: 12390
                                                                            └──Desc: Variable
                                                                               └──Variable: l
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: 12405
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 12404
                                                                               └──Type expr: Variable: 12405
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: 12410
                                                                └──Desc: Variable
                                                                   └──Variable: r
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: 12385
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 12404
                                                                            └──Type expr: Variable: 12385
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 12390
                                                             └──Type expr: Mu
                                                                └──Variable: 12405
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 12404
                                                                            └──Type expr: Variable: 12405
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 12410
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: 12385
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 12404
                                                                               └──Type expr: Variable: 12385
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: 12390
                                                                └──Desc: Variable
                                                                   └──Variable: l
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: 12405
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 12404
                                                                               └──Type expr: Variable: 12405
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: 12410
                                                                └──Desc: Variant
                                                                   └──Variant description:
                                                                      └──Tag: Cons
                                                                      └──Variant row:
                                                                         └──Type expr: Mu
                                                                            └──Variable: 12345
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 12404
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Variable: 12345
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: 12410
                                                                   └──Expression:
                                                                      └──Type expr: Mu
                                                                         └──Variable: 12399
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 12404
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cons
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Variable: 12399
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Nil
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Variable: 12410
                                                                      └──Desc: Tuple
                                                                         └──Expression:
                                                                            └──Type expr: Variable: 12404
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Mu
                                                                               └──Variable: 12405
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: 12404
                                                                                           └──Type expr: Variable: 12405
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Nil
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Variable: 12410
                                                                            └──Desc: Variable
                                                                               └──Variable: r
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 12415
                      └──Type expr: Variable: 12415
                   └──Desc: Variable: id
                └──Abstraction:
                   └──Variables: 12415,12415
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 12415
                         └──Type expr: Variable: 12415
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 12415
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: 12415
                            └──Desc: Variable
                               └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: 12431
                         └──Type expr: Variable: 12428
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: 12434
                            └──Type expr: Variable: 12431
                         └──Type expr: Arrow
                            └──Type expr: Variable: 12434
                            └──Type expr: Variable: 12428
                   └──Desc: Variable: compose
                └──Abstraction:
                   └──Variables: 12428
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: 12431
                            └──Type expr: Variable: 12428
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: 12434
                               └──Type expr: Variable: 12431
                            └──Type expr: Arrow
                               └──Type expr: Variable: 12434
                               └──Type expr: Variable: 12428
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Variable: 12431
                               └──Type expr: Variable: 12428
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 12434
                                  └──Type expr: Variable: 12431
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 12434
                                  └──Type expr: Variable: 12428
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 12434
                                     └──Type expr: Variable: 12431
                                  └──Desc: Variable: g
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 12434
                                     └──Type expr: Variable: 12428
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: 12434
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: 12428
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: 12431
                                                 └──Type expr: Variable: 12428
                                              └──Desc: Variable
                                                 └──Variable: f
                                           └──Expression:
                                              └──Type expr: Variable: 12431
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 12434
                                                       └──Type expr: Variable: 12431
                                                    └──Desc: Variable
                                                       └──Variable: g
                                                 └──Expression:
                                                    └──Type expr: Variable: 12434
                                                    └──Desc: Variable
                                                       └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: 12453
                      └──Type expr: Arrow
                         └──Type expr: Variable: 12454
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Cons
                               └──Type expr: Constructor: present
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: 12453
                                     └──Type expr: Variable: 12454
                               └──Type expr: Variable: 12447
                   └──Desc: Variable: cons
                └──Abstraction:
                   └──Variables: 12453,12453
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: 12453
                         └──Type expr: Arrow
                            └──Type expr: Variable: 12454
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: 12453
                                        └──Type expr: Variable: 12454
                                  └──Type expr: Variable: 12447
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: 12453
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: 12454
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 12453
                                           └──Type expr: Variable: 12454
                                     └──Type expr: Variable: 12447
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: 12454
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 12453
                                              └──Type expr: Variable: 12454
                                        └──Type expr: Variable: 12447
                                  └──Desc: Variant
                                     └──Variant description:
                                        └──Tag: Cons
                                        └──Variant row:
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 12453
                                                    └──Type expr: Variable: 12454
                                              └──Type expr: Variable: 12447
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 12453
                                           └──Type expr: Variable: 12454
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Variable: 12453
                                              └──Desc: Variable
                                                 └──Variable: x
                                           └──Expression:
                                              └──Type expr: Variable: 12454
                                              └──Desc: Variable
                                                 └──Variable: t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: 12623
                         └──Type expr: Constructor: bool
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: 12623
                            └──Type expr: Arrow
                               └──Type expr: Variable: 12623
                               └──Type expr: Constructor: bool
                         └──Type expr: Arrow
                            └──Type expr: Mu
                               └──Variable: 12643
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 12623
                                           └──Type expr: Variable: 12643
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                            └──Type expr: Arrow
                               └──Type expr: Mu
                                  └──Variable: 12653
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 12623
                                              └──Type expr: Variable: 12653
                                        └──Type expr: Variable: 12655
                               └──Type expr: Mu
                                  └──Variable: 12653
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 12623
                                              └──Type expr: Variable: 12653
                                        └──Type expr: Variable: 12655
                   └──Desc: Variable: sort_append
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: 12623
                            └──Type expr: Constructor: bool
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: 12623
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 12623
                                  └──Type expr: Constructor: bool
                            └──Type expr: Arrow
                               └──Type expr: Mu
                                  └──Variable: 12643
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 12623
                                              └──Type expr: Variable: 12643
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                               └──Type expr: Arrow
                                  └──Type expr: Mu
                                     └──Variable: 12653
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: 12623
                                                 └──Type expr: Variable: 12653
                                           └──Type expr: Variable: 12655
                                  └──Type expr: Mu
                                     └──Variable: 12653
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: 12623
                                                 └──Type expr: Variable: 12653
                                           └──Type expr: Variable: 12655
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Variable: 12623
                               └──Type expr: Constructor: bool
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 12623
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 12623
                                     └──Type expr: Constructor: bool
                               └──Type expr: Arrow
                                  └──Type expr: Mu
                                     └──Variable: 12643
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: 12623
                                                 └──Type expr: Variable: 12643
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                                  └──Type expr: Arrow
                                     └──Type expr: Mu
                                        └──Variable: 12653
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 12623
                                                    └──Type expr: Variable: 12653
                                              └──Type expr: Variable: 12655
                                     └──Type expr: Mu
                                        └──Variable: 12653
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 12623
                                                    └──Type expr: Variable: 12653
                                              └──Type expr: Variable: 12655
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 12623
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: 12623
                                        └──Type expr: Constructor: bool
                                  └──Desc: Variable: le
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Mu
                                        └──Variable: 12643
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: 12623
                                                    └──Type expr: Variable: 12643
                                              └──Type expr: Row cons
                                                 └──Label: Nil
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                     └──Type expr: Arrow
                                        └──Type expr: Mu
                                           └──Variable: 12653
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Cons
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 12623
                                                       └──Type expr: Variable: 12653
                                                 └──Type expr: Variable: 12655
                                        └──Type expr: Mu
                                           └──Variable: 12653
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Cons
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 12623
                                                       └──Type expr: Variable: 12653
                                                 └──Type expr: Variable: 12655
                                  └──Desc: Let rec
                                     └──Value bindings:
                                        └──Value binding:
                                           └──Variable: loop
                                           └──Abstraction:
                                              └──Variables: 12632
                                              └──Expression:
                                                 └──Type expr: Arrow
                                                    └──Type expr: Mu
                                                       └──Variable: 12635
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 12623
                                                                   └──Type expr: Variable: 12635
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row uniform
                                                                   └──Type expr: Constructor: absent
                                                    └──Type expr: Arrow
                                                       └──Type expr: Mu
                                                          └──Variable: 12617
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 12623
                                                                      └──Type expr: Variable: 12617
                                                                └──Type expr: Variable: 12632
                                                       └──Type expr: Mu
                                                          └──Variable: 12617
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 12623
                                                                      └──Type expr: Variable: 12617
                                                                └──Type expr: Variable: 12632
                                                 └──Desc: Function
                                                    └──Pattern:
                                                       └──Type expr: Mu
                                                          └──Variable: 12635
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: 12623
                                                                      └──Type expr: Variable: 12635
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
                                                             └──Variable: 12617
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 12623
                                                                         └──Type expr: Variable: 12617
                                                                   └──Type expr: Variable: 12632
                                                          └──Type expr: Mu
                                                             └──Variable: 12617
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 12623
                                                                         └──Type expr: Variable: 12617
                                                                   └──Type expr: Variable: 12632
                                                       └──Desc: Match
                                                          └──Expression:
                                                             └──Type expr: Mu
                                                                └──Variable: 12635
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 12623
                                                                            └──Type expr: Variable: 12635
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                                             └──Desc: Variable
                                                                └──Variable: t
                                                          └──Type expr: Mu
                                                             └──Variable: 12635
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 12623
                                                                         └──Type expr: Variable: 12635
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
                                                                                  └──Variable: 12555
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 12623
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Variable: 12555
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
                                                                                        └──Variable: 12555
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: 12623
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Variable: 12555
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
                                                                         └──Variable: 12617
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 12623
                                                                                     └──Type expr: Variable: 12617
                                                                               └──Type expr: Variable: 12632
                                                                      └──Type expr: Mu
                                                                         └──Variable: 12617
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 12623
                                                                                     └──Type expr: Variable: 12617
                                                                               └──Type expr: Variable: 12632
                                                                   └──Desc: Variable
                                                                      └──Variable: id
                                                                      └──Type expr: Mu
                                                                         └──Variable: 12617
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 12623
                                                                                     └──Type expr: Variable: 12617
                                                                               └──Type expr: Variable: 12632
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
                                                                                  └──Variable: 12555
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 12623
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Variable: 12555
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
                                                                                        └──Variable: 12555
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: 12623
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Variable: 12555
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
                                                                            └──Variable: 12555
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: 12623
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Variable: 12555
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Nil
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Row uniform
                                                                                           └──Type expr: Constructor: absent
                                                                         └──Desc: Tuple
                                                                            └──Pattern:
                                                                               └──Type expr: Variable: 12623
                                                                               └──Desc: Any
                                                                            └──Pattern:
                                                                               └──Type expr: Mu
                                                                                  └──Variable: 12635
                                                                                  └──Type expr: Variant
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Cons
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: 12623
                                                                                              └──Type expr: Variable: 12635
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
                                                                         └──Variable: 12617
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 12623
                                                                                     └──Type expr: Variable: 12617
                                                                               └──Type expr: Variable: 12632
                                                                      └──Type expr: Mu
                                                                         └──Variable: 12617
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 12623
                                                                                     └──Type expr: Variable: 12617
                                                                               └──Type expr: Variable: 12632
                                                                   └──Desc: Let
                                                                      └──Value bindings:
                                                                         └──Value binding:
                                                                            └──Pattern:
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: 12623
                                                                                  └──Type expr: Mu
                                                                                     └──Variable: 12635
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: 12623
                                                                                                 └──Type expr: Variable: 12635
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Nil
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Constructor: unit
                                                                                              └──Type expr: Row uniform
                                                                                                 └──Type expr: Constructor: absent
                                                                               └──Desc: Tuple
                                                                                  └──Pattern:
                                                                                     └──Type expr: Variable: 12623
                                                                                     └──Desc: Variable: pivot
                                                                                  └──Pattern:
                                                                                     └──Type expr: Mu
                                                                                        └──Variable: 12635
                                                                                        └──Type expr: Variant
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Cons
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Tuple
                                                                                                    └──Type expr: Variable: 12623
                                                                                                    └──Type expr: Variable: 12635
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
                                                                                     └──Type expr: Variable: 12623
                                                                                     └──Type expr: Mu
                                                                                        └──Variable: 12635
                                                                                        └──Type expr: Variant
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Cons
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Tuple
                                                                                                    └──Type expr: Variable: 12623
                                                                                                    └──Type expr: Variable: 12635
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
                                                                                              └──Type expr: Variable: 12623
                                                                                              └──Type expr: Constructor: bool
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: 12623
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: 12635
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: 12623
                                                                                                             └──Type expr: Variable: 12635
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
                                                                                                    └──Variable: 12635
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: 12623
                                                                                                                └──Type expr: Variable: 12635
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Nil
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Constructor: unit
                                                                                                             └──Type expr: Row uniform
                                                                                                                └──Type expr: Constructor: absent
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Variable: 12623
                                                                                                       └──Type expr: Constructor: bool
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: 12623
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: 12635
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: 12623
                                                                                                                      └──Type expr: Variable: 12635
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Nil
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Constructor: unit
                                                                                                                   └──Type expr: Row uniform
                                                                                                                      └──Type expr: Constructor: absent
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: select
                                                                                                 └──Type expr: Variable: 12623
                                                                                           └──Expression:
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: 12635
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: 12623
                                                                                                             └──Type expr: Variable: 12635
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
                                                                                           └──Type expr: Variable: 12623
                                                                                           └──Type expr: Constructor: bool
                                                                                        └──Desc: Variable
                                                                                           └──Variable: f
                                                                      └──Expression:
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Mu
                                                                               └──Variable: 12617
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: 12623
                                                                                           └──Type expr: Variable: 12617
                                                                                     └──Type expr: Variable: 12632
                                                                            └──Type expr: Mu
                                                                               └──Variable: 12617
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: 12623
                                                                                           └──Type expr: Variable: 12617
                                                                                     └──Type expr: Variable: 12632
                                                                         └──Desc: Let
                                                                            └──Value bindings:
                                                                               └──Value binding:
                                                                                  └──Pattern:
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Mu
                                                                                           └──Variable: 12635
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: 12623
                                                                                                       └──Type expr: Variable: 12635
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Nil
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Constructor: unit
                                                                                                    └──Type expr: Row uniform
                                                                                                       └──Type expr: Constructor: absent
                                                                                        └──Type expr: Mu
                                                                                           └──Variable: 12635
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: 12623
                                                                                                       └──Type expr: Variable: 12635
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Nil
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Constructor: unit
                                                                                                    └──Type expr: Row uniform
                                                                                                       └──Type expr: Constructor: absent
                                                                                     └──Desc: Tuple
                                                                                        └──Pattern:
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: 12635
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: 12623
                                                                                                          └──Type expr: Variable: 12635
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Nil
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Constructor: unit
                                                                                                       └──Type expr: Row uniform
                                                                                                          └──Type expr: Constructor: absent
                                                                                           └──Desc: Variable: l
                                                                                        └──Pattern:
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: 12635
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: 12623
                                                                                                          └──Type expr: Variable: 12635
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
                                                                                              └──Variable: 12635
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: 12623
                                                                                                          └──Type expr: Variable: 12635
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Nil
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Constructor: unit
                                                                                                       └──Type expr: Row uniform
                                                                                                          └──Type expr: Constructor: absent
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: 12635
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: 12623
                                                                                                          └──Type expr: Variable: 12635
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
                                                                                                    └──Type expr: Variable: 12623
                                                                                                    └──Type expr: Constructor: bool
                                                                                                 └──Type expr: Tuple
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 12635
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 12623
                                                                                                                   └──Type expr: Variable: 12635
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Nil
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Constructor: unit
                                                                                                                └──Type expr: Row uniform
                                                                                                                   └──Type expr: Constructor: absent
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 12635
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 12623
                                                                                                                   └──Type expr: Variable: 12635
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
                                                                                                          └──Variable: 12635
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: 12623
                                                                                                                      └──Type expr: Variable: 12635
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Nil
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Constructor: unit
                                                                                                                   └──Type expr: Row uniform
                                                                                                                      └──Type expr: Constructor: absent
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Arrow
                                                                                                             └──Type expr: Variable: 12623
                                                                                                             └──Type expr: Constructor: bool
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Mu
                                                                                                                └──Variable: 12635
                                                                                                                └──Type expr: Variant
                                                                                                                   └──Type expr: Row cons
                                                                                                                      └──Label: Cons
                                                                                                                      └──Type expr: Constructor: present
                                                                                                                         └──Type expr: Tuple
                                                                                                                            └──Type expr: Variable: 12623
                                                                                                                            └──Type expr: Variable: 12635
                                                                                                                      └──Type expr: Row cons
                                                                                                                         └──Label: Nil
                                                                                                                         └──Type expr: Constructor: present
                                                                                                                            └──Type expr: Constructor: unit
                                                                                                                         └──Type expr: Row uniform
                                                                                                                            └──Type expr: Constructor: absent
                                                                                                             └──Type expr: Mu
                                                                                                                └──Variable: 12635
                                                                                                                └──Type expr: Variant
                                                                                                                   └──Type expr: Row cons
                                                                                                                      └──Label: Cons
                                                                                                                      └──Type expr: Constructor: present
                                                                                                                         └──Type expr: Tuple
                                                                                                                            └──Type expr: Variable: 12623
                                                                                                                            └──Type expr: Variable: 12635
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
                                                                                                       └──Variable: 12635
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 12623
                                                                                                                   └──Type expr: Variable: 12635
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
                                                                                                 └──Type expr: Variable: 12623
                                                                                                 └──Type expr: Constructor: bool
                                                                                              └──Desc: Function
                                                                                                 └──Pattern:
                                                                                                    └──Type expr: Variable: 12623
                                                                                                    └──Desc: Variable: y
                                                                                                 └──Expression:
                                                                                                    └──Type expr: Constructor: bool
                                                                                                    └──Desc: Application
                                                                                                       └──Expression:
                                                                                                          └──Type expr: Arrow
                                                                                                             └──Type expr: Variable: 12623
                                                                                                             └──Type expr: Constructor: bool
                                                                                                          └──Desc: Application
                                                                                                             └──Expression:
                                                                                                                └──Type expr: Arrow
                                                                                                                   └──Type expr: Variable: 12623
                                                                                                                   └──Type expr: Arrow
                                                                                                                      └──Type expr: Variable: 12623
                                                                                                                      └──Type expr: Constructor: bool
                                                                                                                └──Desc: Variable
                                                                                                                   └──Variable: le
                                                                                                             └──Expression:
                                                                                                                └──Type expr: Variable: 12623
                                                                                                                └──Desc: Variable
                                                                                                                   └──Variable: y
                                                                                                       └──Expression:
                                                                                                          └──Type expr: Variable: 12623
                                                                                                          └──Desc: Variable
                                                                                                             └──Variable: pivot
                                                                            └──Expression:
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Mu
                                                                                     └──Variable: 12617
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: 12623
                                                                                                 └──Type expr: Variable: 12617
                                                                                           └──Type expr: Variable: 12632
                                                                                  └──Type expr: Mu
                                                                                     └──Variable: 12617
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: 12623
                                                                                                 └──Type expr: Variable: 12617
                                                                                           └──Type expr: Variable: 12632
                                                                               └──Desc: Application
                                                                                  └──Expression:
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: 12617
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: 12623
                                                                                                          └──Type expr: Variable: 12617
                                                                                                    └──Type expr: Variable: 12632
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: 12617
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: 12623
                                                                                                          └──Type expr: Variable: 12617
                                                                                                    └──Type expr: Variable: 12632
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: 12617
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: 12623
                                                                                                          └──Type expr: Variable: 12617
                                                                                                    └──Type expr: Variable: 12632
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: 12617
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: 12623
                                                                                                          └──Type expr: Variable: 12617
                                                                                                    └──Type expr: Variable: 12632
                                                                                     └──Desc: Application
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: 12617
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: 12623
                                                                                                                └──Type expr: Variable: 12617
                                                                                                          └──Type expr: Variable: 12632
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: 12617
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: 12623
                                                                                                                └──Type expr: Variable: 12617
                                                                                                          └──Type expr: Variable: 12632
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 12617
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 12623
                                                                                                                   └──Type expr: Variable: 12617
                                                                                                             └──Type expr: Variable: 12632
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 12617
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 12623
                                                                                                                   └──Type expr: Variable: 12617
                                                                                                             └──Type expr: Variable: 12632
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 12617
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 12623
                                                                                                                   └──Type expr: Variable: 12617
                                                                                                             └──Type expr: Variable: 12632
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 12617
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 12623
                                                                                                                   └──Type expr: Variable: 12617
                                                                                                             └──Type expr: Variable: 12632
                                                                                           └──Desc: Variable
                                                                                              └──Variable: compose
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: 12617
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: 12623
                                                                                                             └──Type expr: Variable: 12617
                                                                                                       └──Type expr: Variable: 12632
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: 12617
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: 12623
                                                                                                             └──Type expr: Variable: 12617
                                                                                                       └──Type expr: Variable: 12632
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: 12617
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: 12623
                                                                                                             └──Type expr: Variable: 12617
                                                                                                       └──Type expr: Variable: 12632
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: 12617
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: 12623
                                                                                                             └──Type expr: Variable: 12617
                                                                                                       └──Type expr: Variable: 12632
                                                                                           └──Desc: Application
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 12635
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 12623
                                                                                                                   └──Type expr: Variable: 12635
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Nil
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Constructor: unit
                                                                                                                └──Type expr: Row uniform
                                                                                                                   └──Type expr: Constructor: absent
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: 12617
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: 12623
                                                                                                                      └──Type expr: Variable: 12617
                                                                                                                └──Type expr: Variable: 12632
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: 12617
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: 12623
                                                                                                                      └──Type expr: Variable: 12617
                                                                                                                └──Type expr: Variable: 12632
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: loop
                                                                                              └──Expression:
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: 12635
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: 12623
                                                                                                                └──Type expr: Variable: 12635
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
                                                                                           └──Variable: 12617
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: 12623
                                                                                                       └──Type expr: Variable: 12617
                                                                                                 └──Type expr: Variable: 12632
                                                                                        └──Type expr: Mu
                                                                                           └──Variable: 12617
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: 12623
                                                                                                       └──Type expr: Variable: 12617
                                                                                                 └──Type expr: Variable: 12632
                                                                                     └──Desc: Application
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: 12617
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: 12623
                                                                                                                └──Type expr: Variable: 12617
                                                                                                          └──Type expr: Variable: 12632
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: 12617
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: 12623
                                                                                                                └──Type expr: Variable: 12617
                                                                                                          └──Type expr: Variable: 12632
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: 12617
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: 12623
                                                                                                                └──Type expr: Variable: 12617
                                                                                                          └──Type expr: Variable: 12632
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: 12617
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: 12623
                                                                                                                └──Type expr: Variable: 12617
                                                                                                          └──Type expr: Variable: 12632
                                                                                           └──Desc: Application
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: 12617
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: 12623
                                                                                                                      └──Type expr: Variable: 12617
                                                                                                                └──Type expr: Variable: 12632
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: 12617
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: 12623
                                                                                                                      └──Type expr: Variable: 12617
                                                                                                                └──Type expr: Variable: 12632
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: 12617
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: 12623
                                                                                                                         └──Type expr: Variable: 12617
                                                                                                                   └──Type expr: Variable: 12632
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: 12617
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: 12623
                                                                                                                         └──Type expr: Variable: 12617
                                                                                                                   └──Type expr: Variable: 12632
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: 12617
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: 12623
                                                                                                                         └──Type expr: Variable: 12617
                                                                                                                   └──Type expr: Variable: 12632
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: 12617
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: 12623
                                                                                                                         └──Type expr: Variable: 12617
                                                                                                                   └──Type expr: Variable: 12632
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: compose
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 12617
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 12623
                                                                                                                   └──Type expr: Variable: 12617
                                                                                                             └──Type expr: Variable: 12632
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 12617
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 12623
                                                                                                                   └──Type expr: Variable: 12617
                                                                                                             └──Type expr: Variable: 12632
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 12617
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 12623
                                                                                                                   └──Type expr: Variable: 12617
                                                                                                             └──Type expr: Variable: 12632
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 12617
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 12623
                                                                                                                   └──Type expr: Variable: 12617
                                                                                                             └──Type expr: Variable: 12632
                                                                                                 └──Desc: Application
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Variable: 12623
                                                                                                          └──Type expr: Arrow
                                                                                                             └──Type expr: Mu
                                                                                                                └──Variable: 12617
                                                                                                                └──Type expr: Variant
                                                                                                                   └──Type expr: Row cons
                                                                                                                      └──Label: Cons
                                                                                                                      └──Type expr: Constructor: present
                                                                                                                         └──Type expr: Tuple
                                                                                                                            └──Type expr: Variable: 12623
                                                                                                                            └──Type expr: Variable: 12617
                                                                                                                      └──Type expr: Variable: 12632
                                                                                                             └──Type expr: Mu
                                                                                                                └──Variable: 12617
                                                                                                                └──Type expr: Variant
                                                                                                                   └──Type expr: Row cons
                                                                                                                      └──Label: Cons
                                                                                                                      └──Type expr: Constructor: present
                                                                                                                         └──Type expr: Tuple
                                                                                                                            └──Type expr: Variable: 12623
                                                                                                                            └──Type expr: Variable: 12617
                                                                                                                      └──Type expr: Variable: 12632
                                                                                                       └──Desc: Variable
                                                                                                          └──Variable: cons
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: 12617
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: 12623
                                                                                                                         └──Type expr: Variable: 12617
                                                                                                                   └──Type expr: Variable: 12632
                                                                                                          └──Type expr: Variable: 12623
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Variable: 12623
                                                                                                       └──Desc: Variable
                                                                                                          └──Variable: pivot
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: 12617
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: 12623
                                                                                                             └──Type expr: Variable: 12617
                                                                                                       └──Type expr: Variable: 12632
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: 12617
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: 12623
                                                                                                             └──Type expr: Variable: 12617
                                                                                                       └──Type expr: Variable: 12632
                                                                                           └──Desc: Application
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: 12635
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: 12623
                                                                                                                   └──Type expr: Variable: 12635
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Nil
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Constructor: unit
                                                                                                                └──Type expr: Row uniform
                                                                                                                   └──Type expr: Constructor: absent
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: 12617
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: 12623
                                                                                                                      └──Type expr: Variable: 12617
                                                                                                                └──Type expr: Variable: 12632
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: 12617
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: 12623
                                                                                                                      └──Type expr: Variable: 12617
                                                                                                                └──Type expr: Variable: 12632
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: loop
                                                                                              └──Expression:
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: 12635
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: 12623
                                                                                                                └──Type expr: Variable: 12635
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
                                              └──Variable: 12643
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Cons
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 12623
                                                          └──Type expr: Variable: 12643
                                                    └──Type expr: Row cons
                                                       └──Label: Nil
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                           └──Type expr: Arrow
                                              └──Type expr: Mu
                                                 └──Variable: 12653
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 12623
                                                             └──Type expr: Variable: 12653
                                                       └──Type expr: Variable: 12655
                                              └──Type expr: Mu
                                                 └──Variable: 12653
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 12623
                                                             └──Type expr: Variable: 12653
                                                       └──Type expr: Variable: 12655
                                        └──Desc: Variable
                                           └──Variable: loop
                                           └──Type expr: Variable: 12655
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Mu
                         └──Variable: 12670
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Cons
                               └──Type expr: Constructor: present
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: 12681
                                     └──Type expr: Variable: 12670
                               └──Type expr: Row cons
                                  └──Label: Nil
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: 12681
                            └──Type expr: Arrow
                               └──Type expr: Variable: 12681
                               └──Type expr: Constructor: bool
                         └──Type expr: Mu
                            └──Variable: 12664
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: 12681
                                        └──Type expr: Variable: 12664
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Variable: 12720
                   └──Desc: Variable: sort
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Mu
                            └──Variable: 12670
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: 12681
                                        └──Type expr: Variable: 12670
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: 12681
                               └──Type expr: Arrow
                                  └──Type expr: Variable: 12681
                                  └──Type expr: Constructor: bool
                            └──Type expr: Mu
                               └──Variable: 12664
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 12681
                                           └──Type expr: Variable: 12664
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Variable: 12720
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Mu
                               └──Variable: 12670
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: 12681
                                           └──Type expr: Variable: 12670
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
                                  └──Type expr: Variable: 12681
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 12681
                                     └──Type expr: Constructor: bool
                               └──Type expr: Mu
                                  └──Variable: 12664
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: 12681
                                              └──Type expr: Variable: 12664
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: 12720
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: 12681
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: 12681
                                        └──Type expr: Constructor: bool
                                  └──Desc: Variable: le
                               └──Expression:
                                  └──Type expr: Mu
                                     └──Variable: 12664
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: 12681
                                                 └──Type expr: Variable: 12664
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: 12720
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Mu
                                              └──Variable: 12664
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Cons
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 12681
                                                          └──Type expr: Variable: 12664
                                                    └──Type expr: Row cons
                                                       └──Label: Nil
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: 12720
                                           └──Type expr: Mu
                                              └──Variable: 12664
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Cons
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: 12681
                                                          └──Type expr: Variable: 12664
                                                    └──Type expr: Row cons
                                                       └──Label: Nil
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: 12720
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Mu
                                                    └──Variable: 12670
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: 12681
                                                                └──Type expr: Variable: 12670
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                                 └──Type expr: Arrow
                                                    └──Type expr: Mu
                                                       └──Variable: 12664
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 12681
                                                                   └──Type expr: Variable: 12664
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 12720
                                                    └──Type expr: Mu
                                                       └──Variable: 12664
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: 12681
                                                                   └──Type expr: Variable: 12664
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: 12720
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: 12681
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 12681
                                                             └──Type expr: Constructor: bool
                                                       └──Type expr: Arrow
                                                          └──Type expr: Mu
                                                             └──Variable: 12670
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: 12681
                                                                         └──Type expr: Variable: 12670
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                          └──Type expr: Arrow
                                                             └──Type expr: Mu
                                                                └──Variable: 12664
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 12681
                                                                            └──Type expr: Variable: 12664
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 12720
                                                             └──Type expr: Mu
                                                                └──Variable: 12664
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: 12681
                                                                            └──Type expr: Variable: 12664
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: 12720
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: 12681
                                                                └──Type expr: Constructor: bool
                                                             └──Type expr: Arrow
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: 12681
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: 12681
                                                                      └──Type expr: Constructor: bool
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Mu
                                                                      └──Variable: 12670
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: 12681
                                                                                  └──Type expr: Variable: 12670
                                                                            └──Type expr: Row cons
                                                                               └──Label: Nil
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Mu
                                                                         └──Variable: 12664
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 12681
                                                                                     └──Type expr: Variable: 12664
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: 12720
                                                                      └──Type expr: Mu
                                                                         └──Variable: 12664
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: 12681
                                                                                     └──Type expr: Variable: 12664
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: 12720
                                                          └──Desc: Variable
                                                             └──Variable: sort_append
                                                             └──Type expr: Variable: 12681
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: 12681
                                                             └──Type expr: Constructor: bool
                                                          └──Desc: Function
                                                             └──Pattern:
                                                                └──Type expr: Variable: 12681
                                                                └──Desc: Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: bool
                                                                └──Desc: Constant: true
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: 12681
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: 12681
                                                          └──Type expr: Constructor: bool
                                                    └──Desc: Variable
                                                       └──Variable: le
                                           └──Expression:
                                              └──Type expr: Mu
                                                 └──Variable: 12670
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 12681
                                                             └──Type expr: Variable: 12670
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
                                           └──Variable: 12664
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Cons
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: 12681
                                                       └──Type expr: Variable: 12664
                                                 └──Type expr: Row cons
                                                    └──Label: Nil
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Variable: 12720
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Nil
                                              └──Variant row:
                                                 └──Type expr: Mu
                                                    └──Variable: 12699
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: 12681
                                                             └──Type expr: Variant
                                                                └──Type expr: Variable: 12699
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: 12720 |}]