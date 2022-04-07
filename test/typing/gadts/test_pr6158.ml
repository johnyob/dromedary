open! Import
open Util

let%expect_test "" = 
  let str = 
    {|
      type 'a t = T of 'a;;
      type 'a s = S of 'a;;

      type ('a, 'b) eq = 
        | Refl constraint 'a = 'b
      ;;

      let f = 
        fun (Refl : (int s, int t) eq) -> ()
      ;;
    |}
  in
  print_infer_result str;
  [%expect {|
    "Inconsistent equations added by local branches" |}]