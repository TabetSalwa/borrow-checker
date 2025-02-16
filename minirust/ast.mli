open Ast_types

(** This modules parses the input, and provides some support functions for the AST. *)

val ast : program
(** Global AST, as a list of declarations. *)

val global_env : (string, decl) Hashtbl.t
(** Global AST, as a hash table from identifiers to declarations. *)

val dummy_loc : location

(* Accessors. *)

val decl_name : decl -> ident
val decl_lfts : decl -> lifetime list
val decl_loc : decl -> location
val get_struct_def : string -> struct_decl
val get_fun_def : string -> fun_decl
