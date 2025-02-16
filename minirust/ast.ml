open Ast_types

let decl_name = function Dstruct { sname; _ } -> sname | Dfundef { fname; _ } -> fname
let decl_lfts = function Dstruct { slfts; _ } -> slfts | Dfundef { flfts; _ } -> flfts
let decl_loc = function Dstruct { sloc; _ } -> sloc | Dfundef { floc; _ } -> floc

let ast =
  if Array.length Sys.argv != 2 then Error.usage ();
  let filename = Sys.argv.(1) in
  let _, lexbuf = MenhirLib.LexerUtil.read filename in
  try Parser.prog Lexer.token lexbuf
  with Parser.Error ->
    let startp = Lexing.lexeme_start_p lexbuf and endp = Lexing.lexeme_end_p lexbuf in
    Error.error (startp, endp) "Syntax error."

let global_env = Hashtbl.create 17

let () =
  let add id decl =
    if Hashtbl.mem global_env id.id then
      Error.error id.iloc "This identifier is already defined.";
    Hashtbl.add global_env id.id decl
  in
  List.iter (fun decl -> add (decl_name decl) decl) ast

let dummy_loc = Lexing.dummy_pos, Lexing.dummy_pos

module SMap = Map.Make (String)

let get_struct_def id =
  match Hashtbl.find global_env id with Dstruct d -> d | _ -> assert false

let get_fun_def id =
  match Hashtbl.find global_env id with Dfundef d -> d | _ -> assert false
