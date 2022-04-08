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
                └──Variables: a4580
                └──Type expr: Arrow
                   └──Type expr: Constructor: string
                   └──Type expr: Variable: a4580
             └──Primitive name: %failwith
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Variable: select
                └──Abstraction:
                   └──Variables: a4666
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Mu
                            └──Variable: a4667
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a4666
                                        └──Type expr: Variable: a4667
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: a4666
                               └──Type expr: Constructor: bool
                            └──Type expr: Tuple
                               └──Type expr: Variable: a4666
                               └──Type expr: Mu
                                  └──Variable: a4667
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a4666
                                              └──Type expr: Variable: a4667
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Mu
                               └──Variable: a4667
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a4666
                                           └──Type expr: Variable: a4667
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
                                  └──Type expr: Variable: a4666
                                  └──Type expr: Constructor: bool
                               └──Type expr: Tuple
                                  └──Type expr: Variable: a4666
                                  └──Type expr: Mu
                                     └──Variable: a4667
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a4666
                                                 └──Type expr: Variable: a4667
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a4666
                                     └──Type expr: Constructor: bool
                                  └──Desc: Variable: f
                               └──Expression:
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: a4666
                                     └──Type expr: Mu
                                        └──Variable: a4667
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a4666
                                                    └──Type expr: Variable: a4667
                                              └──Type expr: Row cons
                                                 └──Label: Nil
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                  └──Desc: Match
                                     └──Expression:
                                        └──Type expr: Mu
                                           └──Variable: a4667
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Cons
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a4666
                                                       └──Type expr: Variable: a4667
                                                 └──Type expr: Row cons
                                                    └──Label: Nil
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row uniform
                                                       └──Type expr: Constructor: absent
                                        └──Desc: Variable
                                           └──Variable: t1
                                     └──Type expr: Mu
                                        └──Variable: a4667
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a4666
                                                    └──Type expr: Variable: a4667
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
                                                             └──Variable: a4599
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a4666
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Variable: a4599
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
                                                                   └──Variable: a4599
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a4666
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Variable: a4599
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
                                                 └──Type expr: Variable: a4666
                                                 └──Type expr: Mu
                                                    └──Variable: a4667
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a4666
                                                                └──Type expr: Variable: a4667
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
                                                          └──Type expr: Variable: a4666
                                                          └──Type expr: Mu
                                                             └──Variable: a4667
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a4666
                                                                         └──Type expr: Variable: a4667
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                    └──Desc: Variable
                                                       └──Variable: failwith
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a4666
                                                          └──Type expr: Mu
                                                             └──Variable: a4667
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a4666
                                                                         └──Type expr: Variable: a4667
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
                                                             └──Variable: a4599
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a4666
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Variable: a4599
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
                                                                   └──Variable: a4599
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a4666
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Variable: a4599
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
                                                       └──Variable: a4599
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a4666
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Variable: a4599
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Variable: a4666
                                                          └──Desc: Variable: x
                                                       └──Pattern:
                                                          └──Type expr: Mu
                                                             └──Variable: a4667
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a4666
                                                                         └──Type expr: Variable: a4667
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                          └──Desc: Variable: t2
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a4666
                                                 └──Type expr: Mu
                                                    └──Variable: a4667
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a4666
                                                                └──Type expr: Variable: a4667
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
                                                             └──Type expr: Variable: a4666
                                                             └──Type expr: Constructor: bool
                                                          └──Desc: Variable
                                                             └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Variable: a4666
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a4666
                                                       └──Type expr: Mu
                                                          └──Variable: a4667
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a4666
                                                                      └──Type expr: Variable: a4667
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                    └──Desc: Tuple
                                                       └──Expression:
                                                          └──Type expr: Variable: a4666
                                                          └──Desc: Variable
                                                             └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Mu
                                                             └──Variable: a4667
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a4666
                                                                         └──Type expr: Variable: a4667
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
                                                       └──Type expr: Variable: a4666
                                                       └──Type expr: Mu
                                                          └──Variable: a4667
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a4666
                                                                      └──Type expr: Variable: a4667
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
                                                                   └──Type expr: Variable: a4666
                                                                   └──Type expr: Mu
                                                                      └──Variable: a4667
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: a4666
                                                                                  └──Type expr: Variable: a4667
                                                                            └──Type expr: Row cons
                                                                               └──Label: Nil
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                                                                └──Desc: Tuple
                                                                   └──Pattern:
                                                                      └──Type expr: Variable: a4666
                                                                      └──Desc: Variable: y
                                                                   └──Pattern:
                                                                      └──Type expr: Mu
                                                                         └──Variable: a4667
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a4666
                                                                                     └──Type expr: Variable: a4667
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
                                                                      └──Type expr: Variable: a4666
                                                                      └──Type expr: Mu
                                                                         └──Variable: a4667
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a4666
                                                                                     └──Type expr: Variable: a4667
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
                                                                               └──Type expr: Variable: a4666
                                                                               └──Type expr: Constructor: bool
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a4666
                                                                               └──Type expr: Mu
                                                                                  └──Variable: a4667
                                                                                  └──Type expr: Variant
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Cons
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: a4666
                                                                                              └──Type expr: Variable: a4667
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
                                                                                     └──Variable: a4667
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: a4666
                                                                                                 └──Type expr: Variable: a4667
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Nil
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Constructor: unit
                                                                                              └──Type expr: Row uniform
                                                                                                 └──Type expr: Constructor: absent
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Variable: a4666
                                                                                        └──Type expr: Constructor: bool
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Variable: a4666
                                                                                        └──Type expr: Mu
                                                                                           └──Variable: a4667
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: a4666
                                                                                                       └──Type expr: Variable: a4667
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
                                                                                  └──Variable: a4667
                                                                                  └──Type expr: Variant
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Cons
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: a4666
                                                                                              └──Type expr: Variable: a4667
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
                                                                            └──Type expr: Variable: a4666
                                                                            └──Type expr: Constructor: bool
                                                                         └──Desc: Variable
                                                                            └──Variable: f
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a4666
                                                             └──Type expr: Mu
                                                                └──Variable: a4667
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a4666
                                                                            └──Type expr: Variable: a4667
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Variable: a4666
                                                                └──Desc: Variable
                                                                   └──Variable: y
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: a4667
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a4666
                                                                               └──Type expr: Variable: a4667
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
                                                                            └──Variable: a4606
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a4666
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Variable: a4606
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row uniform
                                                                                     └──Type expr: Constructor: absent
                                                                   └──Expression:
                                                                      └──Type expr: Mu
                                                                         └──Variable: a4599
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a4666
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cons
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Variable: a4599
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Nil
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Row uniform
                                                                                        └──Type expr: Constructor: absent
                                                                      └──Desc: Tuple
                                                                         └──Expression:
                                                                            └──Type expr: Variable: a4666
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Mu
                                                                               └──Variable: a4667
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: a4666
                                                                                           └──Type expr: Variable: a4667
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
                   └──Variables: a4725,a4728
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Mu
                            └──Variable: a4737
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Nil
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a4728
                                           └──Type expr: Variable: a4737
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Arrow
                            └──Type expr: Variable: a4725
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a4728
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a4725
                                     └──Type expr: Variable: a4725
                               └──Type expr: Variable: a4725
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Mu
                               └──Variable: a4737
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a4728
                                              └──Type expr: Variable: a4737
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a4725
                               └──Type expr: Arrow
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a4728
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: a4725
                                        └──Type expr: Variable: a4725
                                  └──Type expr: Variable: a4725
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: a4725
                                  └──Desc: Variable: init
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: a4728
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: a4725
                                           └──Type expr: Variable: a4725
                                     └──Type expr: Variable: a4725
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: a4728
                                           └──Type expr: Arrow
                                              └──Type expr: Variable: a4725
                                              └──Type expr: Variable: a4725
                                        └──Desc: Variable: f
                                     └──Expression:
                                        └──Type expr: Variable: a4725
                                        └──Desc: Match
                                           └──Expression:
                                              └──Type expr: Mu
                                                 └──Variable: a4737
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Nil
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a4728
                                                                └──Type expr: Variable: a4737
                                                          └──Type expr: Row uniform
                                                             └──Type expr: Constructor: absent
                                              └──Desc: Variable
                                                 └──Variable: t
                                           └──Type expr: Mu
                                              └──Variable: a4737
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Nil
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a4728
                                                             └──Type expr: Variable: a4737
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
                                                                   └──Variable: a4697
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a4728
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Variable: a4697
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
                                                                         └──Variable: a4697
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a4728
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Variable: a4697
                                                                                     └──Type expr: Row uniform
                                                                                        └──Type expr: Constructor: absent
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                 └──Expression:
                                                    └──Type expr: Variable: a4725
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
                                                                   └──Variable: a4697
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a4728
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Variable: a4697
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
                                                                         └──Variable: a4697
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a4728
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Variable: a4697
                                                                                     └──Type expr: Row uniform
                                                                                        └──Type expr: Constructor: absent
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                       └──Pattern:
                                                          └──Type expr: Mu
                                                             └──Variable: a4697
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a4728
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Variable: a4697
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                                          └──Desc: Tuple
                                                             └──Pattern:
                                                                └──Type expr: Variable: a4728
                                                                └──Desc: Variable: x
                                                             └──Pattern:
                                                                └──Type expr: Mu
                                                                   └──Variable: a4737
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: a4728
                                                                                  └──Type expr: Variable: a4737
                                                                            └──Type expr: Row uniform
                                                                               └──Type expr: Constructor: absent
                                                                └──Desc: Variable: t
                                                 └──Expression:
                                                    └──Type expr: Variable: a4725
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a4725
                                                             └──Type expr: Variable: a4725
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: a4728
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a4725
                                                                      └──Type expr: Variable: a4725
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Variable: a4728
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Variable: a4725
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a4728
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: a4725
                                                                         └──Type expr: Variable: a4725
                                                                   └──Type expr: Variable: a4725
                                                                └──Desc: Application
                                                                   └──Expression:
                                                                      └──Type expr: Arrow
                                                                         └──Type expr: Variable: a4725
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Variable: a4728
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: a4725
                                                                                  └──Type expr: Variable: a4725
                                                                            └──Type expr: Variable: a4725
                                                                      └──Desc: Application
                                                                         └──Expression:
                                                                            └──Type expr: Arrow
                                                                               └──Type expr: Mu
                                                                                  └──Variable: a4737
                                                                                  └──Type expr: Variant
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Nil
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: a4728
                                                                                                 └──Type expr: Variable: a4737
                                                                                           └──Type expr: Row uniform
                                                                                              └──Type expr: Constructor: absent
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Variable: a4725
                                                                                  └──Type expr: Arrow
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Variable: a4728
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Variable: a4725
                                                                                           └──Type expr: Variable: a4725
                                                                                     └──Type expr: Variable: a4725
                                                                            └──Desc: Variable
                                                                               └──Variable: fold_right
                                                                         └──Expression:
                                                                            └──Type expr: Mu
                                                                               └──Variable: a4737
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Nil
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Cons
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: a4728
                                                                                              └──Type expr: Variable: a4737
                                                                                        └──Type expr: Row uniform
                                                                                           └──Type expr: Constructor: absent
                                                                            └──Desc: Variable
                                                                               └──Variable: t
                                                                   └──Expression:
                                                                      └──Type expr: Variable: a4725
                                                                      └──Desc: Variable
                                                                         └──Variable: init
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: a4728
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a4725
                                                                      └──Type expr: Variable: a4725
                                                                └──Desc: Variable
                                                                   └──Variable: f
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Mu
                         └──Variable: a4759
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Nil
                               └──Type expr: Constructor: present
                                  └──Type expr: Constructor: unit
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a4852
                                        └──Type expr: Variable: a4759
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a4852
                            └──Type expr: Constructor: bool
                         └──Type expr: Tuple
                            └──Type expr: Mu
                               └──Variable: a4833
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a4852
                                           └──Type expr: Variable: a4833
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Variable: a4838
                            └──Type expr: Mu
                               └──Variable: a4853
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a4852
                                           └──Type expr: Variable: a4853
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Variable: a4858
                   └──Desc: Variable: partition
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Mu
                            └──Variable: a4759
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Nil
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a4852
                                           └──Type expr: Variable: a4759
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: a4852
                               └──Type expr: Constructor: bool
                            └──Type expr: Tuple
                               └──Type expr: Mu
                                  └──Variable: a4833
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a4852
                                              └──Type expr: Variable: a4833
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: a4838
                               └──Type expr: Mu
                                  └──Variable: a4853
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a4852
                                              └──Type expr: Variable: a4853
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: a4858
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Mu
                               └──Variable: a4759
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a4852
                                              └──Type expr: Variable: a4759
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                            └──Desc: Variable: t
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a4852
                                  └──Type expr: Constructor: bool
                               └──Type expr: Tuple
                                  └──Type expr: Mu
                                     └──Variable: a4833
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a4852
                                                 └──Type expr: Variable: a4833
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: a4838
                                  └──Type expr: Mu
                                     └──Variable: a4853
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a4852
                                                 └──Type expr: Variable: a4853
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: a4858
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a4852
                                     └──Type expr: Constructor: bool
                                  └──Desc: Variable: f
                               └──Expression:
                                  └──Type expr: Tuple
                                     └──Type expr: Mu
                                        └──Variable: a4833
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a4852
                                                    └──Type expr: Variable: a4833
                                              └──Type expr: Row cons
                                                 └──Label: Nil
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Variable: a4838
                                     └──Type expr: Mu
                                        └──Variable: a4853
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a4852
                                                    └──Type expr: Variable: a4853
                                              └──Type expr: Row cons
                                                 └──Label: Nil
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Variable: a4858
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Arrow
                                              └──Type expr: Variable: a4852
                                              └──Type expr: Arrow
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: a4833
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a4852
                                                                   └──Type expr: Variable: a4833
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a4838
                                                    └──Type expr: Mu
                                                       └──Variable: a4853
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a4852
                                                                   └──Type expr: Variable: a4853
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a4858
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: a4833
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a4852
                                                                   └──Type expr: Variable: a4833
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a4838
                                                    └──Type expr: Mu
                                                       └──Variable: a4853
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a4852
                                                                   └──Type expr: Variable: a4853
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a4858
                                           └──Type expr: Tuple
                                              └──Type expr: Mu
                                                 └──Variable: a4833
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a4852
                                                             └──Type expr: Variable: a4833
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: a4838
                                              └──Type expr: Mu
                                                 └──Variable: a4853
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a4852
                                                             └──Type expr: Variable: a4853
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: a4858
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: a4833
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a4852
                                                                   └──Type expr: Variable: a4833
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a4838
                                                    └──Type expr: Mu
                                                       └──Variable: a4853
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a4852
                                                                   └──Type expr: Variable: a4853
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a4858
                                                 └──Type expr: Arrow
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: a4852
                                                       └──Type expr: Arrow
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: a4833
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a4852
                                                                            └──Type expr: Variable: a4833
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a4838
                                                             └──Type expr: Mu
                                                                └──Variable: a4853
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a4852
                                                                            └──Type expr: Variable: a4853
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a4858
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: a4833
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a4852
                                                                            └──Type expr: Variable: a4833
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a4838
                                                             └──Type expr: Mu
                                                                └──Variable: a4853
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a4852
                                                                            └──Type expr: Variable: a4853
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a4858
                                                    └──Type expr: Tuple
                                                       └──Type expr: Mu
                                                          └──Variable: a4833
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a4852
                                                                      └──Type expr: Variable: a4833
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: a4838
                                                       └──Type expr: Mu
                                                          └──Variable: a4853
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a4852
                                                                      └──Type expr: Variable: a4853
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: a4858
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Mu
                                                          └──Variable: a4759
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a4852
                                                                         └──Type expr: Variable: a4759
                                                                   └──Type expr: Row uniform
                                                                      └──Type expr: Constructor: absent
                                                       └──Type expr: Arrow
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: a4833
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a4852
                                                                            └──Type expr: Variable: a4833
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a4838
                                                             └──Type expr: Mu
                                                                └──Variable: a4853
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a4852
                                                                            └──Type expr: Variable: a4853
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a4858
                                                          └──Type expr: Arrow
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a4852
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Mu
                                                                         └──Variable: a4833
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a4852
                                                                                     └──Type expr: Variable: a4833
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a4838
                                                                      └──Type expr: Mu
                                                                         └──Variable: a4853
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a4852
                                                                                     └──Type expr: Variable: a4853
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a4858
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Mu
                                                                         └──Variable: a4833
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a4852
                                                                                     └──Type expr: Variable: a4833
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a4838
                                                                      └──Type expr: Mu
                                                                         └──Variable: a4853
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a4852
                                                                                     └──Type expr: Variable: a4853
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a4858
                                                             └──Type expr: Tuple
                                                                └──Type expr: Mu
                                                                   └──Variable: a4833
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a4852
                                                                               └──Type expr: Variable: a4833
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: a4838
                                                                └──Type expr: Mu
                                                                   └──Variable: a4853
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a4852
                                                                               └──Type expr: Variable: a4853
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: a4858
                                                    └──Desc: Variable
                                                       └──Variable: fold_right
                                                       └──Type expr: Tuple
                                                          └──Type expr: Mu
                                                             └──Variable: a4833
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a4852
                                                                         └──Type expr: Variable: a4833
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: a4838
                                                          └──Type expr: Mu
                                                             └──Variable: a4853
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a4852
                                                                         └──Type expr: Variable: a4853
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: a4858
                                                       └──Type expr: Variable: a4852
                                                 └──Expression:
                                                    └──Type expr: Mu
                                                       └──Variable: a4759
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a4852
                                                                      └──Type expr: Variable: a4759
                                                                └──Type expr: Row uniform
                                                                   └──Type expr: Constructor: absent
                                                    └──Desc: Variable
                                                       └──Variable: t
                                           └──Expression:
                                              └──Type expr: Tuple
                                                 └──Type expr: Mu
                                                    └──Variable: a4833
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a4852
                                                                └──Type expr: Variable: a4833
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: a4838
                                                 └──Type expr: Mu
                                                    └──Variable: a4853
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a4852
                                                                └──Type expr: Variable: a4853
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: a4858
                                              └──Desc: Tuple
                                                 └──Expression:
                                                    └──Type expr: Mu
                                                       └──Variable: a4833
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a4852
                                                                   └──Type expr: Variable: a4833
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a4838
                                                    └──Desc: Variant
                                                       └──Variant description:
                                                          └──Tag: Nil
                                                          └──Variant row:
                                                             └──Type expr: Mu
                                                                └──Variable: a4782
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a4852
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Variable: a4782
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: a4838
                                                 └──Expression:
                                                    └──Type expr: Mu
                                                       └──Variable: a4853
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a4852
                                                                   └──Type expr: Variable: a4853
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a4858
                                                    └──Desc: Variant
                                                       └──Variant description:
                                                          └──Tag: Nil
                                                          └──Variant row:
                                                             └──Type expr: Mu
                                                                └──Variable: a4793
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a4852
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Variable: a4793
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: a4858
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Variable: a4852
                                           └──Type expr: Arrow
                                              └──Type expr: Tuple
                                                 └──Type expr: Mu
                                                    └──Variable: a4833
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a4852
                                                                └──Type expr: Variable: a4833
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: a4838
                                                 └──Type expr: Mu
                                                    └──Variable: a4853
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a4852
                                                                └──Type expr: Variable: a4853
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: a4858
                                              └──Type expr: Tuple
                                                 └──Type expr: Mu
                                                    └──Variable: a4833
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a4852
                                                                └──Type expr: Variable: a4833
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: a4838
                                                 └──Type expr: Mu
                                                    └──Variable: a4853
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a4852
                                                                └──Type expr: Variable: a4853
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Variable: a4858
                                        └──Desc: Function
                                           └──Pattern:
                                              └──Type expr: Variable: a4852
                                              └──Desc: Variable: x
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: a4833
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a4852
                                                                   └──Type expr: Variable: a4833
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a4838
                                                    └──Type expr: Mu
                                                       └──Variable: a4853
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a4852
                                                                   └──Type expr: Variable: a4853
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a4858
                                                 └──Type expr: Tuple
                                                    └──Type expr: Mu
                                                       └──Variable: a4833
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a4852
                                                                   └──Type expr: Variable: a4833
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a4838
                                                    └──Type expr: Mu
                                                       └──Variable: a4853
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a4852
                                                                   └──Type expr: Variable: a4853
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a4858
                                              └──Desc: Function
                                                 └──Pattern:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Mu
                                                          └──Variable: a4833
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a4852
                                                                      └──Type expr: Variable: a4833
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: a4838
                                                       └──Type expr: Mu
                                                          └──Variable: a4853
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a4852
                                                                      └──Type expr: Variable: a4853
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: a4858
                                                    └──Desc: Tuple
                                                       └──Pattern:
                                                          └──Type expr: Mu
                                                             └──Variable: a4833
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a4852
                                                                         └──Type expr: Variable: a4833
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: a4838
                                                          └──Desc: Variable: l
                                                       └──Pattern:
                                                          └──Type expr: Mu
                                                             └──Variable: a4853
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a4852
                                                                         └──Type expr: Variable: a4853
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Variable: a4858
                                                          └──Desc: Variable: r
                                                 └──Expression:
                                                    └──Type expr: Tuple
                                                       └──Type expr: Mu
                                                          └──Variable: a4833
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a4852
                                                                      └──Type expr: Variable: a4833
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: a4838
                                                       └──Type expr: Mu
                                                          └──Variable: a4853
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a4852
                                                                      └──Type expr: Variable: a4853
                                                                └──Type expr: Row cons
                                                                   └──Label: Nil
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Constructor: unit
                                                                   └──Type expr: Variable: a4858
                                                    └──Desc: If
                                                       └──Expression:
                                                          └──Type expr: Constructor: bool
                                                          └──Desc: Application
                                                             └──Expression:
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: a4852
                                                                   └──Type expr: Constructor: bool
                                                                └──Desc: Variable
                                                                   └──Variable: f
                                                             └──Expression:
                                                                └──Type expr: Variable: a4852
                                                                └──Desc: Variable
                                                                   └──Variable: x
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: a4833
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a4852
                                                                            └──Type expr: Variable: a4833
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a4838
                                                             └──Type expr: Mu
                                                                └──Variable: a4853
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a4852
                                                                            └──Type expr: Variable: a4853
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a4858
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: a4833
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a4852
                                                                               └──Type expr: Variable: a4833
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: a4838
                                                                └──Desc: Variant
                                                                   └──Variant description:
                                                                      └──Tag: Cons
                                                                      └──Variant row:
                                                                         └──Type expr: Mu
                                                                            └──Variable: a4782
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a4852
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Variable: a4782
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a4838
                                                                   └──Expression:
                                                                      └──Type expr: Mu
                                                                         └──Variable: a4827
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a4852
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cons
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Variable: a4827
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Nil
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Variable: a4838
                                                                      └──Desc: Tuple
                                                                         └──Expression:
                                                                            └──Type expr: Variable: a4852
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Mu
                                                                               └──Variable: a4833
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: a4852
                                                                                           └──Type expr: Variable: a4833
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Nil
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Variable: a4838
                                                                            └──Desc: Variable
                                                                               └──Variable: l
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: a4853
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a4852
                                                                               └──Type expr: Variable: a4853
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: a4858
                                                                └──Desc: Variable
                                                                   └──Variable: r
                                                       └──Expression:
                                                          └──Type expr: Tuple
                                                             └──Type expr: Mu
                                                                └──Variable: a4833
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a4852
                                                                            └──Type expr: Variable: a4833
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a4838
                                                             └──Type expr: Mu
                                                                └──Variable: a4853
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a4852
                                                                            └──Type expr: Variable: a4853
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a4858
                                                          └──Desc: Tuple
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: a4833
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a4852
                                                                               └──Type expr: Variable: a4833
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: a4838
                                                                └──Desc: Variable
                                                                   └──Variable: l
                                                             └──Expression:
                                                                └──Type expr: Mu
                                                                   └──Variable: a4853
                                                                   └──Type expr: Variant
                                                                      └──Type expr: Row cons
                                                                         └──Label: Cons
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a4852
                                                                               └──Type expr: Variable: a4853
                                                                         └──Type expr: Row cons
                                                                            └──Label: Nil
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Constructor: unit
                                                                            └──Type expr: Variable: a4858
                                                                └──Desc: Variant
                                                                   └──Variant description:
                                                                      └──Tag: Cons
                                                                      └──Variant row:
                                                                         └──Type expr: Mu
                                                                            └──Variable: a4793
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a4852
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Variable: a4793
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a4858
                                                                   └──Expression:
                                                                      └──Type expr: Mu
                                                                         └──Variable: a4847
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a4852
                                                                            └──Type expr: Variant
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Cons
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Variable: a4847
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Nil
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Constructor: unit
                                                                                     └──Type expr: Variable: a4858
                                                                      └──Desc: Tuple
                                                                         └──Expression:
                                                                            └──Type expr: Variable: a4852
                                                                            └──Desc: Variable
                                                                               └──Variable: x
                                                                         └──Expression:
                                                                            └──Type expr: Mu
                                                                               └──Variable: a4853
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: a4852
                                                                                           └──Type expr: Variable: a4853
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Nil
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Variable: a4858
                                                                            └──Desc: Variable
                                                                               └──Variable: r
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: a4863
                      └──Type expr: Variable: a4863
                   └──Desc: Variable: id
                └──Abstraction:
                   └──Variables: a4863,a4863
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a4863
                         └──Type expr: Variable: a4863
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a4863
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Variable: a4863
                            └──Desc: Variable
                               └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: a4879
                         └──Type expr: Variable: a4876
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a4882
                            └──Type expr: Variable: a4879
                         └──Type expr: Arrow
                            └──Type expr: Variable: a4882
                            └──Type expr: Variable: a4876
                   └──Desc: Variable: compose
                └──Abstraction:
                   └──Variables: a4876
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a4879
                            └──Type expr: Variable: a4876
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: a4882
                               └──Type expr: Variable: a4879
                            └──Type expr: Arrow
                               └──Type expr: Variable: a4882
                               └──Type expr: Variable: a4876
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a4879
                               └──Type expr: Variable: a4876
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a4882
                                  └──Type expr: Variable: a4879
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a4882
                                  └──Type expr: Variable: a4876
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a4882
                                     └──Type expr: Variable: a4879
                                  └──Desc: Variable: g
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a4882
                                     └──Type expr: Variable: a4876
                                  └──Desc: Function
                                     └──Pattern:
                                        └──Type expr: Variable: a4882
                                        └──Desc: Variable: x
                                     └──Expression:
                                        └──Type expr: Variable: a4876
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Variable: a4879
                                                 └──Type expr: Variable: a4876
                                              └──Desc: Variable
                                                 └──Variable: f
                                           └──Expression:
                                              └──Type expr: Variable: a4879
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: a4882
                                                       └──Type expr: Variable: a4879
                                                    └──Desc: Variable
                                                       └──Variable: g
                                                 └──Expression:
                                                    └──Type expr: Variable: a4882
                                                    └──Desc: Variable
                                                       └──Variable: x
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Variable: a4901
                      └──Type expr: Arrow
                         └──Type expr: Variable: a4902
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Cons
                               └──Type expr: Constructor: present
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: a4901
                                     └──Type expr: Variable: a4902
                               └──Type expr: Variable: a4895
                   └──Desc: Variable: cons
                └──Abstraction:
                   └──Variables: a4901,a4901
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Variable: a4901
                         └──Type expr: Arrow
                            └──Type expr: Variable: a4902
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a4901
                                        └──Type expr: Variable: a4902
                                  └──Type expr: Variable: a4895
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Variable: a4901
                            └──Desc: Variable: x
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a4902
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a4901
                                           └──Type expr: Variable: a4902
                                     └──Type expr: Variable: a4895
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Variable: a4902
                                  └──Desc: Variable: t
                               └──Expression:
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a4901
                                              └──Type expr: Variable: a4902
                                        └──Type expr: Variable: a4895
                                  └──Desc: Variant
                                     └──Variant description:
                                        └──Tag: Cons
                                        └──Variant row:
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a4901
                                                    └──Type expr: Variable: a4902
                                              └──Type expr: Variable: a4895
                                     └──Expression:
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a4901
                                           └──Type expr: Variable: a4902
                                        └──Desc: Tuple
                                           └──Expression:
                                              └──Type expr: Variable: a4901
                                              └──Desc: Variable
                                                 └──Variable: x
                                           └──Expression:
                                              └──Type expr: Variable: a4902
                                              └──Desc: Variable
                                                 └──Variable: t
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Arrow
                         └──Type expr: Variable: a5071
                         └──Type expr: Constructor: bool
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a5071
                            └──Type expr: Arrow
                               └──Type expr: Variable: a5071
                               └──Type expr: Constructor: bool
                         └──Type expr: Arrow
                            └──Type expr: Mu
                               └──Variable: a5091
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a5071
                                           └──Type expr: Variable: a5091
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Row uniform
                                           └──Type expr: Constructor: absent
                            └──Type expr: Arrow
                               └──Type expr: Mu
                                  └──Variable: a5101
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a5071
                                              └──Type expr: Variable: a5101
                                        └──Type expr: Variable: a5103
                               └──Type expr: Mu
                                  └──Variable: a5101
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a5071
                                              └──Type expr: Variable: a5101
                                        └──Type expr: Variable: a5103
                   └──Desc: Variable: sort_append
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a5071
                            └──Type expr: Constructor: bool
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: a5071
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a5071
                                  └──Type expr: Constructor: bool
                            └──Type expr: Arrow
                               └──Type expr: Mu
                                  └──Variable: a5091
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a5071
                                              └──Type expr: Variable: a5091
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Row uniform
                                              └──Type expr: Constructor: absent
                               └──Type expr: Arrow
                                  └──Type expr: Mu
                                     └──Variable: a5101
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a5071
                                                 └──Type expr: Variable: a5101
                                           └──Type expr: Variable: a5103
                                  └──Type expr: Mu
                                     └──Variable: a5101
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a5071
                                                 └──Type expr: Variable: a5101
                                           └──Type expr: Variable: a5103
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Arrow
                               └──Type expr: Variable: a5071
                               └──Type expr: Constructor: bool
                            └──Desc: Variable: f
                         └──Expression:
                            └──Type expr: Arrow
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a5071
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a5071
                                     └──Type expr: Constructor: bool
                               └──Type expr: Arrow
                                  └──Type expr: Mu
                                     └──Variable: a5091
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a5071
                                                 └──Type expr: Variable: a5091
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Row uniform
                                                 └──Type expr: Constructor: absent
                                  └──Type expr: Arrow
                                     └──Type expr: Mu
                                        └──Variable: a5101
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a5071
                                                    └──Type expr: Variable: a5101
                                              └──Type expr: Variable: a5103
                                     └──Type expr: Mu
                                        └──Variable: a5101
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a5071
                                                    └──Type expr: Variable: a5101
                                              └──Type expr: Variable: a5103
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a5071
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: a5071
                                        └──Type expr: Constructor: bool
                                  └──Desc: Variable: le
                               └──Expression:
                                  └──Type expr: Arrow
                                     └──Type expr: Mu
                                        └──Variable: a5091
                                        └──Type expr: Variant
                                           └──Type expr: Row cons
                                              └──Label: Cons
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Tuple
                                                    └──Type expr: Variable: a5071
                                                    └──Type expr: Variable: a5091
                                              └──Type expr: Row cons
                                                 └──Label: Nil
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Constructor: unit
                                                 └──Type expr: Row uniform
                                                    └──Type expr: Constructor: absent
                                     └──Type expr: Arrow
                                        └──Type expr: Mu
                                           └──Variable: a5101
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Cons
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a5071
                                                       └──Type expr: Variable: a5101
                                                 └──Type expr: Variable: a5103
                                        └──Type expr: Mu
                                           └──Variable: a5101
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Cons
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a5071
                                                       └──Type expr: Variable: a5101
                                                 └──Type expr: Variable: a5103
                                  └──Desc: Let rec
                                     └──Value bindings:
                                        └──Value binding:
                                           └──Variable: loop
                                           └──Abstraction:
                                              └──Variables: a5080
                                              └──Expression:
                                                 └──Type expr: Arrow
                                                    └──Type expr: Mu
                                                       └──Variable: a5083
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a5071
                                                                   └──Type expr: Variable: a5083
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Row uniform
                                                                   └──Type expr: Constructor: absent
                                                    └──Type expr: Arrow
                                                       └──Type expr: Mu
                                                          └──Variable: a5065
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a5071
                                                                      └──Type expr: Variable: a5065
                                                                └──Type expr: Variable: a5080
                                                       └──Type expr: Mu
                                                          └──Variable: a5065
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a5071
                                                                      └──Type expr: Variable: a5065
                                                                └──Type expr: Variable: a5080
                                                 └──Desc: Function
                                                    └──Pattern:
                                                       └──Type expr: Mu
                                                          └──Variable: a5083
                                                          └──Type expr: Variant
                                                             └──Type expr: Row cons
                                                                └──Label: Cons
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Tuple
                                                                      └──Type expr: Variable: a5071
                                                                      └──Type expr: Variable: a5083
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
                                                             └──Variable: a5065
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a5071
                                                                         └──Type expr: Variable: a5065
                                                                   └──Type expr: Variable: a5080
                                                          └──Type expr: Mu
                                                             └──Variable: a5065
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a5071
                                                                         └──Type expr: Variable: a5065
                                                                   └──Type expr: Variable: a5080
                                                       └──Desc: Match
                                                          └──Expression:
                                                             └──Type expr: Mu
                                                                └──Variable: a5083
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a5071
                                                                            └──Type expr: Variable: a5083
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Row uniform
                                                                            └──Type expr: Constructor: absent
                                                             └──Desc: Variable
                                                                └──Variable: t
                                                          └──Type expr: Mu
                                                             └──Variable: a5083
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a5071
                                                                         └──Type expr: Variable: a5083
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
                                                                                  └──Variable: a5003
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a5071
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Variable: a5003
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
                                                                                        └──Variable: a5003
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: a5071
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Variable: a5003
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
                                                                         └──Variable: a5065
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a5071
                                                                                     └──Type expr: Variable: a5065
                                                                               └──Type expr: Variable: a5080
                                                                      └──Type expr: Mu
                                                                         └──Variable: a5065
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a5071
                                                                                     └──Type expr: Variable: a5065
                                                                               └──Type expr: Variable: a5080
                                                                   └──Desc: Variable
                                                                      └──Variable: id
                                                                      └──Type expr: Mu
                                                                         └──Variable: a5065
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a5071
                                                                                     └──Type expr: Variable: a5065
                                                                               └──Type expr: Variable: a5080
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
                                                                                  └──Variable: a5003
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a5071
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Variable: a5003
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
                                                                                        └──Variable: a5003
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: a5071
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Variable: a5003
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
                                                                            └──Variable: a5003
                                                                            └──Type expr: Tuple
                                                                               └──Type expr: Variable: a5071
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Variable: a5003
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Nil
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Constructor: unit
                                                                                        └──Type expr: Row uniform
                                                                                           └──Type expr: Constructor: absent
                                                                         └──Desc: Tuple
                                                                            └──Pattern:
                                                                               └──Type expr: Variable: a5071
                                                                               └──Desc: Any
                                                                            └──Pattern:
                                                                               └──Type expr: Mu
                                                                                  └──Variable: a5083
                                                                                  └──Type expr: Variant
                                                                                     └──Type expr: Row cons
                                                                                        └──Label: Cons
                                                                                        └──Type expr: Constructor: present
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: a5071
                                                                                              └──Type expr: Variable: a5083
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
                                                                         └──Variable: a5065
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a5071
                                                                                     └──Type expr: Variable: a5065
                                                                               └──Type expr: Variable: a5080
                                                                      └──Type expr: Mu
                                                                         └──Variable: a5065
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a5071
                                                                                     └──Type expr: Variable: a5065
                                                                               └──Type expr: Variable: a5080
                                                                   └──Desc: Let
                                                                      └──Value bindings:
                                                                         └──Value binding:
                                                                            └──Pattern:
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: a5071
                                                                                  └──Type expr: Mu
                                                                                     └──Variable: a5083
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: a5071
                                                                                                 └──Type expr: Variable: a5083
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Nil
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Constructor: unit
                                                                                              └──Type expr: Row uniform
                                                                                                 └──Type expr: Constructor: absent
                                                                               └──Desc: Tuple
                                                                                  └──Pattern:
                                                                                     └──Type expr: Variable: a5071
                                                                                     └──Desc: Variable: pivot
                                                                                  └──Pattern:
                                                                                     └──Type expr: Mu
                                                                                        └──Variable: a5083
                                                                                        └──Type expr: Variant
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Cons
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Tuple
                                                                                                    └──Type expr: Variable: a5071
                                                                                                    └──Type expr: Variable: a5083
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
                                                                                     └──Type expr: Variable: a5071
                                                                                     └──Type expr: Mu
                                                                                        └──Variable: a5083
                                                                                        └──Type expr: Variant
                                                                                           └──Type expr: Row cons
                                                                                              └──Label: Cons
                                                                                              └──Type expr: Constructor: present
                                                                                                 └──Type expr: Tuple
                                                                                                    └──Type expr: Variable: a5071
                                                                                                    └──Type expr: Variable: a5083
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
                                                                                              └──Type expr: Variable: a5071
                                                                                              └──Type expr: Constructor: bool
                                                                                           └──Type expr: Tuple
                                                                                              └──Type expr: Variable: a5071
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a5083
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a5071
                                                                                                             └──Type expr: Variable: a5083
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
                                                                                                    └──Variable: a5083
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a5071
                                                                                                                └──Type expr: Variable: a5083
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Nil
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Constructor: unit
                                                                                                             └──Type expr: Row uniform
                                                                                                                └──Type expr: Constructor: absent
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Variable: a5071
                                                                                                       └──Type expr: Constructor: bool
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: a5071
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: a5083
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a5071
                                                                                                                      └──Type expr: Variable: a5083
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Nil
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Constructor: unit
                                                                                                                   └──Type expr: Row uniform
                                                                                                                      └──Type expr: Constructor: absent
                                                                                              └──Desc: Variable
                                                                                                 └──Variable: select
                                                                                                 └──Type expr: Variable: a5071
                                                                                           └──Expression:
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a5083
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a5071
                                                                                                             └──Type expr: Variable: a5083
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
                                                                                           └──Type expr: Variable: a5071
                                                                                           └──Type expr: Constructor: bool
                                                                                        └──Desc: Variable
                                                                                           └──Variable: f
                                                                      └──Expression:
                                                                         └──Type expr: Arrow
                                                                            └──Type expr: Mu
                                                                               └──Variable: a5065
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: a5071
                                                                                           └──Type expr: Variable: a5065
                                                                                     └──Type expr: Variable: a5080
                                                                            └──Type expr: Mu
                                                                               └──Variable: a5065
                                                                               └──Type expr: Variant
                                                                                  └──Type expr: Row cons
                                                                                     └──Label: Cons
                                                                                     └──Type expr: Constructor: present
                                                                                        └──Type expr: Tuple
                                                                                           └──Type expr: Variable: a5071
                                                                                           └──Type expr: Variable: a5065
                                                                                     └──Type expr: Variable: a5080
                                                                         └──Desc: Let
                                                                            └──Value bindings:
                                                                               └──Value binding:
                                                                                  └──Pattern:
                                                                                     └──Type expr: Tuple
                                                                                        └──Type expr: Mu
                                                                                           └──Variable: a5083
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: a5071
                                                                                                       └──Type expr: Variable: a5083
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Nil
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Constructor: unit
                                                                                                    └──Type expr: Row uniform
                                                                                                       └──Type expr: Constructor: absent
                                                                                        └──Type expr: Mu
                                                                                           └──Variable: a5083
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: a5071
                                                                                                       └──Type expr: Variable: a5083
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Nil
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Constructor: unit
                                                                                                    └──Type expr: Row uniform
                                                                                                       └──Type expr: Constructor: absent
                                                                                     └──Desc: Tuple
                                                                                        └──Pattern:
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: a5083
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a5071
                                                                                                          └──Type expr: Variable: a5083
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Nil
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Constructor: unit
                                                                                                       └──Type expr: Row uniform
                                                                                                          └──Type expr: Constructor: absent
                                                                                           └──Desc: Variable: l
                                                                                        └──Pattern:
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: a5083
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a5071
                                                                                                          └──Type expr: Variable: a5083
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
                                                                                              └──Variable: a5083
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a5071
                                                                                                          └──Type expr: Variable: a5083
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Nil
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Constructor: unit
                                                                                                       └──Type expr: Row uniform
                                                                                                          └──Type expr: Constructor: absent
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: a5083
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a5071
                                                                                                          └──Type expr: Variable: a5083
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
                                                                                                    └──Type expr: Variable: a5071
                                                                                                    └──Type expr: Constructor: bool
                                                                                                 └──Type expr: Tuple
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a5083
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a5071
                                                                                                                   └──Type expr: Variable: a5083
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Nil
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Constructor: unit
                                                                                                                └──Type expr: Row uniform
                                                                                                                   └──Type expr: Constructor: absent
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a5083
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a5071
                                                                                                                   └──Type expr: Variable: a5083
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
                                                                                                          └──Variable: a5083
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a5071
                                                                                                                      └──Type expr: Variable: a5083
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Nil
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Constructor: unit
                                                                                                                   └──Type expr: Row uniform
                                                                                                                      └──Type expr: Constructor: absent
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Arrow
                                                                                                             └──Type expr: Variable: a5071
                                                                                                             └──Type expr: Constructor: bool
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Mu
                                                                                                                └──Variable: a5083
                                                                                                                └──Type expr: Variant
                                                                                                                   └──Type expr: Row cons
                                                                                                                      └──Label: Cons
                                                                                                                      └──Type expr: Constructor: present
                                                                                                                         └──Type expr: Tuple
                                                                                                                            └──Type expr: Variable: a5071
                                                                                                                            └──Type expr: Variable: a5083
                                                                                                                      └──Type expr: Row cons
                                                                                                                         └──Label: Nil
                                                                                                                         └──Type expr: Constructor: present
                                                                                                                            └──Type expr: Constructor: unit
                                                                                                                         └──Type expr: Row uniform
                                                                                                                            └──Type expr: Constructor: absent
                                                                                                             └──Type expr: Mu
                                                                                                                └──Variable: a5083
                                                                                                                └──Type expr: Variant
                                                                                                                   └──Type expr: Row cons
                                                                                                                      └──Label: Cons
                                                                                                                      └──Type expr: Constructor: present
                                                                                                                         └──Type expr: Tuple
                                                                                                                            └──Type expr: Variable: a5071
                                                                                                                            └──Type expr: Variable: a5083
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
                                                                                                       └──Variable: a5083
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a5071
                                                                                                                   └──Type expr: Variable: a5083
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
                                                                                                 └──Type expr: Variable: a5071
                                                                                                 └──Type expr: Constructor: bool
                                                                                              └──Desc: Function
                                                                                                 └──Pattern:
                                                                                                    └──Type expr: Variable: a5071
                                                                                                    └──Desc: Variable: y
                                                                                                 └──Expression:
                                                                                                    └──Type expr: Constructor: bool
                                                                                                    └──Desc: Application
                                                                                                       └──Expression:
                                                                                                          └──Type expr: Arrow
                                                                                                             └──Type expr: Variable: a5071
                                                                                                             └──Type expr: Constructor: bool
                                                                                                          └──Desc: Application
                                                                                                             └──Expression:
                                                                                                                └──Type expr: Arrow
                                                                                                                   └──Type expr: Variable: a5071
                                                                                                                   └──Type expr: Arrow
                                                                                                                      └──Type expr: Variable: a5071
                                                                                                                      └──Type expr: Constructor: bool
                                                                                                                └──Desc: Variable
                                                                                                                   └──Variable: le
                                                                                                             └──Expression:
                                                                                                                └──Type expr: Variable: a5071
                                                                                                                └──Desc: Variable
                                                                                                                   └──Variable: y
                                                                                                       └──Expression:
                                                                                                          └──Type expr: Variable: a5071
                                                                                                          └──Desc: Variable
                                                                                                             └──Variable: pivot
                                                                            └──Expression:
                                                                               └──Type expr: Arrow
                                                                                  └──Type expr: Mu
                                                                                     └──Variable: a5065
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: a5071
                                                                                                 └──Type expr: Variable: a5065
                                                                                           └──Type expr: Variable: a5080
                                                                                  └──Type expr: Mu
                                                                                     └──Variable: a5065
                                                                                     └──Type expr: Variant
                                                                                        └──Type expr: Row cons
                                                                                           └──Label: Cons
                                                                                           └──Type expr: Constructor: present
                                                                                              └──Type expr: Tuple
                                                                                                 └──Type expr: Variable: a5071
                                                                                                 └──Type expr: Variable: a5065
                                                                                           └──Type expr: Variable: a5080
                                                                               └──Desc: Application
                                                                                  └──Expression:
                                                                                     └──Type expr: Arrow
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: a5065
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a5071
                                                                                                          └──Type expr: Variable: a5065
                                                                                                    └──Type expr: Variable: a5080
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: a5065
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a5071
                                                                                                          └──Type expr: Variable: a5065
                                                                                                    └──Type expr: Variable: a5080
                                                                                        └──Type expr: Arrow
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: a5065
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a5071
                                                                                                          └──Type expr: Variable: a5065
                                                                                                    └──Type expr: Variable: a5080
                                                                                           └──Type expr: Mu
                                                                                              └──Variable: a5065
                                                                                              └──Type expr: Variant
                                                                                                 └──Type expr: Row cons
                                                                                                    └──Label: Cons
                                                                                                    └──Type expr: Constructor: present
                                                                                                       └──Type expr: Tuple
                                                                                                          └──Type expr: Variable: a5071
                                                                                                          └──Type expr: Variable: a5065
                                                                                                    └──Type expr: Variable: a5080
                                                                                     └──Desc: Application
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a5065
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a5071
                                                                                                                └──Type expr: Variable: a5065
                                                                                                          └──Type expr: Variable: a5080
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a5065
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a5071
                                                                                                                └──Type expr: Variable: a5065
                                                                                                          └──Type expr: Variable: a5080
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a5065
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a5071
                                                                                                                   └──Type expr: Variable: a5065
                                                                                                             └──Type expr: Variable: a5080
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a5065
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a5071
                                                                                                                   └──Type expr: Variable: a5065
                                                                                                             └──Type expr: Variable: a5080
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a5065
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a5071
                                                                                                                   └──Type expr: Variable: a5065
                                                                                                             └──Type expr: Variable: a5080
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a5065
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a5071
                                                                                                                   └──Type expr: Variable: a5065
                                                                                                             └──Type expr: Variable: a5080
                                                                                           └──Desc: Variable
                                                                                              └──Variable: compose
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a5065
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a5071
                                                                                                             └──Type expr: Variable: a5065
                                                                                                       └──Type expr: Variable: a5080
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a5065
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a5071
                                                                                                             └──Type expr: Variable: a5065
                                                                                                       └──Type expr: Variable: a5080
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a5065
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a5071
                                                                                                             └──Type expr: Variable: a5065
                                                                                                       └──Type expr: Variable: a5080
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a5065
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a5071
                                                                                                             └──Type expr: Variable: a5065
                                                                                                       └──Type expr: Variable: a5080
                                                                                           └──Desc: Application
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a5083
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a5071
                                                                                                                   └──Type expr: Variable: a5083
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Nil
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Constructor: unit
                                                                                                                └──Type expr: Row uniform
                                                                                                                   └──Type expr: Constructor: absent
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: a5065
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a5071
                                                                                                                      └──Type expr: Variable: a5065
                                                                                                                └──Type expr: Variable: a5080
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: a5065
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a5071
                                                                                                                      └──Type expr: Variable: a5065
                                                                                                                └──Type expr: Variable: a5080
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: loop
                                                                                              └──Expression:
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a5083
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a5071
                                                                                                                └──Type expr: Variable: a5083
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
                                                                                           └──Variable: a5065
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: a5071
                                                                                                       └──Type expr: Variable: a5065
                                                                                                 └──Type expr: Variable: a5080
                                                                                        └──Type expr: Mu
                                                                                           └──Variable: a5065
                                                                                           └──Type expr: Variant
                                                                                              └──Type expr: Row cons
                                                                                                 └──Label: Cons
                                                                                                 └──Type expr: Constructor: present
                                                                                                    └──Type expr: Tuple
                                                                                                       └──Type expr: Variable: a5071
                                                                                                       └──Type expr: Variable: a5065
                                                                                                 └──Type expr: Variable: a5080
                                                                                     └──Desc: Application
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a5065
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a5071
                                                                                                                └──Type expr: Variable: a5065
                                                                                                          └──Type expr: Variable: a5080
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a5065
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a5071
                                                                                                                └──Type expr: Variable: a5065
                                                                                                          └──Type expr: Variable: a5080
                                                                                              └──Type expr: Arrow
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a5065
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a5071
                                                                                                                └──Type expr: Variable: a5065
                                                                                                          └──Type expr: Variable: a5080
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a5065
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a5071
                                                                                                                └──Type expr: Variable: a5065
                                                                                                          └──Type expr: Variable: a5080
                                                                                           └──Desc: Application
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: a5065
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a5071
                                                                                                                      └──Type expr: Variable: a5065
                                                                                                                └──Type expr: Variable: a5080
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: a5065
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a5071
                                                                                                                      └──Type expr: Variable: a5065
                                                                                                                └──Type expr: Variable: a5080
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: a5065
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: a5071
                                                                                                                         └──Type expr: Variable: a5065
                                                                                                                   └──Type expr: Variable: a5080
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: a5065
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: a5071
                                                                                                                         └──Type expr: Variable: a5065
                                                                                                                   └──Type expr: Variable: a5080
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: a5065
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: a5071
                                                                                                                         └──Type expr: Variable: a5065
                                                                                                                   └──Type expr: Variable: a5080
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: a5065
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: a5071
                                                                                                                         └──Type expr: Variable: a5065
                                                                                                                   └──Type expr: Variable: a5080
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: compose
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a5065
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a5071
                                                                                                                   └──Type expr: Variable: a5065
                                                                                                             └──Type expr: Variable: a5080
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a5065
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a5071
                                                                                                                   └──Type expr: Variable: a5065
                                                                                                             └──Type expr: Variable: a5080
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a5065
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a5071
                                                                                                                   └──Type expr: Variable: a5065
                                                                                                             └──Type expr: Variable: a5080
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a5065
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a5071
                                                                                                                   └──Type expr: Variable: a5065
                                                                                                             └──Type expr: Variable: a5080
                                                                                                 └──Desc: Application
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Arrow
                                                                                                          └──Type expr: Variable: a5071
                                                                                                          └──Type expr: Arrow
                                                                                                             └──Type expr: Mu
                                                                                                                └──Variable: a5065
                                                                                                                └──Type expr: Variant
                                                                                                                   └──Type expr: Row cons
                                                                                                                      └──Label: Cons
                                                                                                                      └──Type expr: Constructor: present
                                                                                                                         └──Type expr: Tuple
                                                                                                                            └──Type expr: Variable: a5071
                                                                                                                            └──Type expr: Variable: a5065
                                                                                                                      └──Type expr: Variable: a5080
                                                                                                             └──Type expr: Mu
                                                                                                                └──Variable: a5065
                                                                                                                └──Type expr: Variant
                                                                                                                   └──Type expr: Row cons
                                                                                                                      └──Label: Cons
                                                                                                                      └──Type expr: Constructor: present
                                                                                                                         └──Type expr: Tuple
                                                                                                                            └──Type expr: Variable: a5071
                                                                                                                            └──Type expr: Variable: a5065
                                                                                                                      └──Type expr: Variable: a5080
                                                                                                       └──Desc: Variable
                                                                                                          └──Variable: cons
                                                                                                          └──Type expr: Mu
                                                                                                             └──Variable: a5065
                                                                                                             └──Type expr: Variant
                                                                                                                └──Type expr: Row cons
                                                                                                                   └──Label: Cons
                                                                                                                   └──Type expr: Constructor: present
                                                                                                                      └──Type expr: Tuple
                                                                                                                         └──Type expr: Variable: a5071
                                                                                                                         └──Type expr: Variable: a5065
                                                                                                                   └──Type expr: Variable: a5080
                                                                                                          └──Type expr: Variable: a5071
                                                                                                    └──Expression:
                                                                                                       └──Type expr: Variable: a5071
                                                                                                       └──Desc: Variable
                                                                                                          └──Variable: pivot
                                                                                        └──Expression:
                                                                                           └──Type expr: Arrow
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a5065
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a5071
                                                                                                             └──Type expr: Variable: a5065
                                                                                                       └──Type expr: Variable: a5080
                                                                                              └──Type expr: Mu
                                                                                                 └──Variable: a5065
                                                                                                 └──Type expr: Variant
                                                                                                    └──Type expr: Row cons
                                                                                                       └──Label: Cons
                                                                                                       └──Type expr: Constructor: present
                                                                                                          └──Type expr: Tuple
                                                                                                             └──Type expr: Variable: a5071
                                                                                                             └──Type expr: Variable: a5065
                                                                                                       └──Type expr: Variable: a5080
                                                                                           └──Desc: Application
                                                                                              └──Expression:
                                                                                                 └──Type expr: Arrow
                                                                                                    └──Type expr: Mu
                                                                                                       └──Variable: a5083
                                                                                                       └──Type expr: Variant
                                                                                                          └──Type expr: Row cons
                                                                                                             └──Label: Cons
                                                                                                             └──Type expr: Constructor: present
                                                                                                                └──Type expr: Tuple
                                                                                                                   └──Type expr: Variable: a5071
                                                                                                                   └──Type expr: Variable: a5083
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Nil
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Constructor: unit
                                                                                                                └──Type expr: Row uniform
                                                                                                                   └──Type expr: Constructor: absent
                                                                                                    └──Type expr: Arrow
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: a5065
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a5071
                                                                                                                      └──Type expr: Variable: a5065
                                                                                                                └──Type expr: Variable: a5080
                                                                                                       └──Type expr: Mu
                                                                                                          └──Variable: a5065
                                                                                                          └──Type expr: Variant
                                                                                                             └──Type expr: Row cons
                                                                                                                └──Label: Cons
                                                                                                                └──Type expr: Constructor: present
                                                                                                                   └──Type expr: Tuple
                                                                                                                      └──Type expr: Variable: a5071
                                                                                                                      └──Type expr: Variable: a5065
                                                                                                                └──Type expr: Variable: a5080
                                                                                                 └──Desc: Variable
                                                                                                    └──Variable: loop
                                                                                              └──Expression:
                                                                                                 └──Type expr: Mu
                                                                                                    └──Variable: a5083
                                                                                                    └──Type expr: Variant
                                                                                                       └──Type expr: Row cons
                                                                                                          └──Label: Cons
                                                                                                          └──Type expr: Constructor: present
                                                                                                             └──Type expr: Tuple
                                                                                                                └──Type expr: Variable: a5071
                                                                                                                └──Type expr: Variable: a5083
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
                                              └──Variable: a5091
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Cons
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a5071
                                                          └──Type expr: Variable: a5091
                                                    └──Type expr: Row cons
                                                       └──Label: Nil
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Row uniform
                                                          └──Type expr: Constructor: absent
                                           └──Type expr: Arrow
                                              └──Type expr: Mu
                                                 └──Variable: a5101
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a5071
                                                             └──Type expr: Variable: a5101
                                                       └──Type expr: Variable: a5103
                                              └──Type expr: Mu
                                                 └──Variable: a5101
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a5071
                                                             └──Type expr: Variable: a5101
                                                       └──Type expr: Variable: a5103
                                        └──Desc: Variable
                                           └──Variable: loop
                                           └──Type expr: Variable: a5103
       └──Structure item: Let
          └──Value bindings:
             └──Value binding:
                └──Pattern:
                   └──Type expr: Arrow
                      └──Type expr: Mu
                         └──Variable: a5118
                         └──Type expr: Variant
                            └──Type expr: Row cons
                               └──Label: Cons
                               └──Type expr: Constructor: present
                                  └──Type expr: Tuple
                                     └──Type expr: Variable: a5129
                                     └──Type expr: Variable: a5118
                               └──Type expr: Row cons
                                  └──Label: Nil
                                  └──Type expr: Constructor: present
                                     └──Type expr: Constructor: unit
                                  └──Type expr: Row uniform
                                     └──Type expr: Constructor: absent
                      └──Type expr: Arrow
                         └──Type expr: Arrow
                            └──Type expr: Variable: a5129
                            └──Type expr: Arrow
                               └──Type expr: Variable: a5129
                               └──Type expr: Constructor: bool
                         └──Type expr: Mu
                            └──Variable: a5112
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a5129
                                        └──Type expr: Variable: a5112
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Variable: a5168
                   └──Desc: Variable: sort
                └──Abstraction:
                   └──Variables:
                   └──Expression:
                      └──Type expr: Arrow
                         └──Type expr: Mu
                            └──Variable: a5118
                            └──Type expr: Variant
                               └──Type expr: Row cons
                                  └──Label: Cons
                                  └──Type expr: Constructor: present
                                     └──Type expr: Tuple
                                        └──Type expr: Variable: a5129
                                        └──Type expr: Variable: a5118
                                  └──Type expr: Row cons
                                     └──Label: Nil
                                     └──Type expr: Constructor: present
                                        └──Type expr: Constructor: unit
                                     └──Type expr: Row uniform
                                        └──Type expr: Constructor: absent
                         └──Type expr: Arrow
                            └──Type expr: Arrow
                               └──Type expr: Variable: a5129
                               └──Type expr: Arrow
                                  └──Type expr: Variable: a5129
                                  └──Type expr: Constructor: bool
                            └──Type expr: Mu
                               └──Variable: a5112
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a5129
                                           └──Type expr: Variable: a5112
                                     └──Type expr: Row cons
                                        └──Label: Nil
                                        └──Type expr: Constructor: present
                                           └──Type expr: Constructor: unit
                                        └──Type expr: Variable: a5168
                      └──Desc: Function
                         └──Pattern:
                            └──Type expr: Mu
                               └──Variable: a5118
                               └──Type expr: Variant
                                  └──Type expr: Row cons
                                     └──Label: Cons
                                     └──Type expr: Constructor: present
                                        └──Type expr: Tuple
                                           └──Type expr: Variable: a5129
                                           └──Type expr: Variable: a5118
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
                                  └──Type expr: Variable: a5129
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a5129
                                     └──Type expr: Constructor: bool
                               └──Type expr: Mu
                                  └──Variable: a5112
                                  └──Type expr: Variant
                                     └──Type expr: Row cons
                                        └──Label: Cons
                                        └──Type expr: Constructor: present
                                           └──Type expr: Tuple
                                              └──Type expr: Variable: a5129
                                              └──Type expr: Variable: a5112
                                        └──Type expr: Row cons
                                           └──Label: Nil
                                           └──Type expr: Constructor: present
                                              └──Type expr: Constructor: unit
                                           └──Type expr: Variable: a5168
                            └──Desc: Function
                               └──Pattern:
                                  └──Type expr: Arrow
                                     └──Type expr: Variable: a5129
                                     └──Type expr: Arrow
                                        └──Type expr: Variable: a5129
                                        └──Type expr: Constructor: bool
                                  └──Desc: Variable: le
                               └──Expression:
                                  └──Type expr: Mu
                                     └──Variable: a5112
                                     └──Type expr: Variant
                                        └──Type expr: Row cons
                                           └──Label: Cons
                                           └──Type expr: Constructor: present
                                              └──Type expr: Tuple
                                                 └──Type expr: Variable: a5129
                                                 └──Type expr: Variable: a5112
                                           └──Type expr: Row cons
                                              └──Label: Nil
                                              └──Type expr: Constructor: present
                                                 └──Type expr: Constructor: unit
                                              └──Type expr: Variable: a5168
                                  └──Desc: Application
                                     └──Expression:
                                        └──Type expr: Arrow
                                           └──Type expr: Mu
                                              └──Variable: a5112
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Cons
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a5129
                                                          └──Type expr: Variable: a5112
                                                    └──Type expr: Row cons
                                                       └──Label: Nil
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: a5168
                                           └──Type expr: Mu
                                              └──Variable: a5112
                                              └──Type expr: Variant
                                                 └──Type expr: Row cons
                                                    └──Label: Cons
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Tuple
                                                          └──Type expr: Variable: a5129
                                                          └──Type expr: Variable: a5112
                                                    └──Type expr: Row cons
                                                       └──Label: Nil
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Constructor: unit
                                                       └──Type expr: Variable: a5168
                                        └──Desc: Application
                                           └──Expression:
                                              └──Type expr: Arrow
                                                 └──Type expr: Mu
                                                    └──Variable: a5118
                                                    └──Type expr: Variant
                                                       └──Type expr: Row cons
                                                          └──Label: Cons
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Tuple
                                                                └──Type expr: Variable: a5129
                                                                └──Type expr: Variable: a5118
                                                          └──Type expr: Row cons
                                                             └──Label: Nil
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Constructor: unit
                                                             └──Type expr: Row uniform
                                                                └──Type expr: Constructor: absent
                                                 └──Type expr: Arrow
                                                    └──Type expr: Mu
                                                       └──Variable: a5112
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a5129
                                                                   └──Type expr: Variable: a5112
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a5168
                                                    └──Type expr: Mu
                                                       └──Variable: a5112
                                                       └──Type expr: Variant
                                                          └──Type expr: Row cons
                                                             └──Label: Cons
                                                             └──Type expr: Constructor: present
                                                                └──Type expr: Tuple
                                                                   └──Type expr: Variable: a5129
                                                                   └──Type expr: Variable: a5112
                                                             └──Type expr: Row cons
                                                                └──Label: Nil
                                                                └──Type expr: Constructor: present
                                                                   └──Type expr: Constructor: unit
                                                                └──Type expr: Variable: a5168
                                              └──Desc: Application
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: a5129
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a5129
                                                             └──Type expr: Constructor: bool
                                                       └──Type expr: Arrow
                                                          └──Type expr: Mu
                                                             └──Variable: a5118
                                                             └──Type expr: Variant
                                                                └──Type expr: Row cons
                                                                   └──Label: Cons
                                                                   └──Type expr: Constructor: present
                                                                      └──Type expr: Tuple
                                                                         └──Type expr: Variable: a5129
                                                                         └──Type expr: Variable: a5118
                                                                   └──Type expr: Row cons
                                                                      └──Label: Nil
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Constructor: unit
                                                                      └──Type expr: Row uniform
                                                                         └──Type expr: Constructor: absent
                                                          └──Type expr: Arrow
                                                             └──Type expr: Mu
                                                                └──Variable: a5112
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a5129
                                                                            └──Type expr: Variable: a5112
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a5168
                                                             └──Type expr: Mu
                                                                └──Variable: a5112
                                                                └──Type expr: Variant
                                                                   └──Type expr: Row cons
                                                                      └──Label: Cons
                                                                      └──Type expr: Constructor: present
                                                                         └──Type expr: Tuple
                                                                            └──Type expr: Variable: a5129
                                                                            └──Type expr: Variable: a5112
                                                                      └──Type expr: Row cons
                                                                         └──Label: Nil
                                                                         └──Type expr: Constructor: present
                                                                            └──Type expr: Constructor: unit
                                                                         └──Type expr: Variable: a5168
                                                    └──Desc: Application
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Arrow
                                                                └──Type expr: Variable: a5129
                                                                └──Type expr: Constructor: bool
                                                             └──Type expr: Arrow
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Variable: a5129
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Variable: a5129
                                                                      └──Type expr: Constructor: bool
                                                                └──Type expr: Arrow
                                                                   └──Type expr: Mu
                                                                      └──Variable: a5118
                                                                      └──Type expr: Variant
                                                                         └──Type expr: Row cons
                                                                            └──Label: Cons
                                                                            └──Type expr: Constructor: present
                                                                               └──Type expr: Tuple
                                                                                  └──Type expr: Variable: a5129
                                                                                  └──Type expr: Variable: a5118
                                                                            └──Type expr: Row cons
                                                                               └──Label: Nil
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Constructor: unit
                                                                               └──Type expr: Row uniform
                                                                                  └──Type expr: Constructor: absent
                                                                   └──Type expr: Arrow
                                                                      └──Type expr: Mu
                                                                         └──Variable: a5112
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a5129
                                                                                     └──Type expr: Variable: a5112
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a5168
                                                                      └──Type expr: Mu
                                                                         └──Variable: a5112
                                                                         └──Type expr: Variant
                                                                            └──Type expr: Row cons
                                                                               └──Label: Cons
                                                                               └──Type expr: Constructor: present
                                                                                  └──Type expr: Tuple
                                                                                     └──Type expr: Variable: a5129
                                                                                     └──Type expr: Variable: a5112
                                                                               └──Type expr: Row cons
                                                                                  └──Label: Nil
                                                                                  └──Type expr: Constructor: present
                                                                                     └──Type expr: Constructor: unit
                                                                                  └──Type expr: Variable: a5168
                                                          └──Desc: Variable
                                                             └──Variable: sort_append
                                                             └──Type expr: Variable: a5129
                                                       └──Expression:
                                                          └──Type expr: Arrow
                                                             └──Type expr: Variable: a5129
                                                             └──Type expr: Constructor: bool
                                                          └──Desc: Function
                                                             └──Pattern:
                                                                └──Type expr: Variable: a5129
                                                                └──Desc: Variable: x
                                                             └──Expression:
                                                                └──Type expr: Constructor: bool
                                                                └──Desc: Constant: true
                                                 └──Expression:
                                                    └──Type expr: Arrow
                                                       └──Type expr: Variable: a5129
                                                       └──Type expr: Arrow
                                                          └──Type expr: Variable: a5129
                                                          └──Type expr: Constructor: bool
                                                    └──Desc: Variable
                                                       └──Variable: le
                                           └──Expression:
                                              └──Type expr: Mu
                                                 └──Variable: a5118
                                                 └──Type expr: Variant
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a5129
                                                             └──Type expr: Variable: a5118
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
                                           └──Variable: a5112
                                           └──Type expr: Variant
                                              └──Type expr: Row cons
                                                 └──Label: Cons
                                                 └──Type expr: Constructor: present
                                                    └──Type expr: Tuple
                                                       └──Type expr: Variable: a5129
                                                       └──Type expr: Variable: a5112
                                                 └──Type expr: Row cons
                                                    └──Label: Nil
                                                    └──Type expr: Constructor: present
                                                       └──Type expr: Constructor: unit
                                                    └──Type expr: Variable: a5168
                                        └──Desc: Variant
                                           └──Variant description:
                                              └──Tag: Nil
                                              └──Variant row:
                                                 └──Type expr: Mu
                                                    └──Variable: a5147
                                                    └──Type expr: Row cons
                                                       └──Label: Cons
                                                       └──Type expr: Constructor: present
                                                          └──Type expr: Tuple
                                                             └──Type expr: Variable: a5129
                                                             └──Type expr: Variant
                                                                └──Type expr: Variable: a5147
                                                       └──Type expr: Row cons
                                                          └──Label: Nil
                                                          └──Type expr: Constructor: present
                                                             └──Type expr: Constructor: unit
                                                          └──Type expr: Variable: a5168 |}]