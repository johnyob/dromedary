open! Import
open Util

let%expect_test "" = 
  let str = 
    {|
      type 'a t = 
        | C of 'b 'c 'o. unit constraint 'a = (('b -> 'o) -> 'o) -> ('c -> 'o) -> 'o 
      ;;

      let (type 'a 'o) f = 
        fun (C () : (('a -> 'o) -> 'o) t) (k : 'a -> 'o) -> 
          (k (fun x -> x) : 'o)
      ;; 
    |}
  in
  print_infer_result str;
  [%expect {|
    ("Cannot unify types"
     ("Type_expr.decode type_expr1" (Type 16234 (Var 16234)))
     ("Type_expr.decode type_expr2" (Type 16233 (Var 16233)))) |}]