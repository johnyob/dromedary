(** This module is used by all expect tests for parsing *)

(** Given Dromedary expression as a string, prints out it's parsetree. *)
val print_expression_parsetree : string -> unit

(** Given Dromedary structure as a string, prints out it's parsetree. *)
val print_structure_parsetree : string -> unit

(** Prints the tokens parser from the given string. *)
val print_tokens : string -> unit
