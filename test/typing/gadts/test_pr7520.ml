open! Import
open Util

let%expect_test "" = 
  let str = 
    {|
      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;
      type empty = (int, string) eq;;

      external hole : 'a. 'a = "%hole";;

      let f = 
        fun t ->
          match t with (`Foo (_ : empty) -> hole)
      ;;
    |}
  in
  print_infer_result str;
  [%expect {| "parse error" |}]