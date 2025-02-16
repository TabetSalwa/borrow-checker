open Lexing

let usage () =
  Printf.eprintf "Usage: minirust <filename>\n";
  exit 1

let error (start, end_) format =
  let start = { start with pos_bol = start.pos_bol - 1 } in
  let end_ = { end_ with pos_bol = end_.pos_bol - 1 } in
  Printf.eprintf "%s" (MenhirLib.LexerUtil.range (start, end_));
  Printf.kfprintf
    (fun _ ->
      Printf.eprintf "\n";
      exit 1)
    stderr format
