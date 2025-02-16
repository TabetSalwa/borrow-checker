open Ast_types

let () = Typecheck.go

let () =
  List.iter
    (fun d ->
      match d with
      | Dfundef fd ->
          let mir = Emit_minimir.emit_fun fd in
          Borrowck.borrowck mir
      | _ -> ())
    Ast.ast
