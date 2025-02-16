open Type
open Ast
open Ast_types
open Minimir

(* Make sure the AST is type-checked. *)
let () = Typecheck.go

module SMap = Map.Make (String)

type env = { locals : local SMap.t; brk : label option }

let saturate_outlives ol =
  (* Floyd-Warshall algorithm. *)
  LMap.fold
    (fun b _ acc ->
      LMap.fold
        (fun a _ acc ->
          if LSet.mem b (LMap.find a acc) then
            LSet.fold (fun c acc -> add_outlives_edge a c acc) (LMap.find b acc) acc
          else acc)
        acc acc)
    ol ol

let all_outlives_fn f =
  let res =
    List.fold_left (fun acc lft -> add_outlives_edge lft lft acc) LMap.empty f.flfts
  in
  let res =
    List.fold_left
      (fun acc (_, _, typ) -> outlives_union acc (implied_outlives typ))
      res f.fformals
  in
  let res = outlives_union res (implied_outlives f.freturn) in
  let res =
    List.fold_left (fun acc (l1, l2) -> add_outlives_edge l1 l2 acc) res f.foutlives
  in
  saturate_outlives res

let rec freshen_lfts = function
  | (Tbool | Ti32 | Tunit) as typ -> typ
  | Tborrow (_, mut, typ) -> Tborrow (fresh_lft (), mut, freshen_lfts typ)
  | Tstruct (id, _) ->
      Tstruct (id, List.map (fun _ -> fresh_lft ()) (get_struct_def id).slfts)

let emit_fun fd =
  let mlocals = Hashtbl.create 7 in
  List.iter (fun (id, _, typ) -> Hashtbl.add mlocals (Lparam id.id) typ) fd.fformals;
  Hashtbl.add mlocals Lret fd.freturn;
  let cnt_locals = ref (-1) in
  let fresh_local typ =
    incr cnt_locals;
    let r = Lvar !cnt_locals in
    Hashtbl.add mlocals r (freshen_lfts typ);
    r
  in

  let instrs = Queue.create () in
  let fresh_instr_ref () =
    let id = Queue.length instrs in
    let r = ref None in
    Queue.push r instrs;
    id, r
  in
  let emit loc instr =
    let id, r = fresh_instr_ref () in
    r := Some (instr, loc);
    id
  in

  let rec translate_place env expr =
    match expr.edesc with
    | Evar x -> (fun next -> next), PlLocal (SMap.find x.id env.locals)
    | Edot (e, f) ->
        let k, pl = translate_place env e in
        k, PlField (pl, f.id)
    | Ederef e ->
        let k, pl = translate_place env e in
        k, PlDeref pl
    | _ ->
        let pl = PlLocal (fresh_local (Option.get expr.etyp)) in
        (fun next -> translate_expr env (Some pl) next expr), pl
  and translate_expr env dest next expr =
    let emit = emit expr.eloc in
    let scoped_tmp typ next =
      let l = fresh_local typ in
      emit @@ Ideinit (l, next), l
    in
    let get_dest next =
      match dest, expr.etyp with
      | None, Some typ ->
          let next, l = scoped_tmp typ next in
          next, PlLocal l
      | Some x, _ -> next, x
      | None, None -> assert false
    in
    let return_unit () =
      match dest with Some dest -> emit @@ Iassign (dest, RVunit, next) | None -> next
    in
    match expr.edesc with
    | Evar _ | Edot _ | Ederef _ ->
        let next, dest = get_dest next in
        let k, pl = translate_place env expr in
        k @@ emit @@ Iassign (dest, RVplace pl, next)
    | Econst cst ->
        let next, dest = get_dest next in
        emit @@ Iassign (dest, RVconst cst, next)
    | Eunit -> return_unit ()
    | Eborrow (mut, e) ->
        let next, dest = get_dest next in
        let k, pl = translate_place env e in
        k @@ emit @@ Iassign (dest, RVborrow (mut, pl), next)
    | Ebinop (op, e1, e2) ->
        let next, dest = get_dest next in
        let next, l1 = scoped_tmp Ti32 next in
        let next, l2 = scoped_tmp Ti32 next in
        let next = emit @@ Iassign (dest, RVbinop (op, l1, l2), next) in
        let next = translate_expr env (Some (PlLocal l2)) next e2 in
        translate_expr env (Some (PlLocal l1)) next e1
    | Eunop (op, e) ->
        let next, dest = get_dest next in
        let next, l = scoped_tmp (match op with Uneg -> Ti32 | Unot -> Tbool) next in
        let next = emit @@ Iassign (dest, RVunop (op, l), next) in
        translate_expr env (Some (PlLocal l)) next e
    | Eand (e1, e2) ->
        let next, dest = get_dest next in
        let next, l1 = scoped_tmp Tbool next in
        let mid = translate_expr env (Some dest) next e2 in
        let shortcut = emit @@ Iassign (dest, RVconst (Cbool false), next) in
        let if_ = emit @@ Iif (l1, mid, shortcut) in
        translate_expr env (Some (PlLocal l1)) if_ e1
    | Eor (e1, e2) ->
        let next, dest = get_dest next in
        let next, l1 = scoped_tmp Tbool next in
        let mid = translate_expr env (Some dest) next e2 in
        let shortcut = emit @@ Iassign (dest, RVconst (Cbool true), next) in
        let next = emit @@ Iif (l1, shortcut, mid) in
        translate_expr env (Some (PlLocal l1)) next e1
    | Eassign (e1, e2) ->
        let next = return_unit () in
        let k, pl = translate_place env e1 in
        k @@ translate_expr env (Some pl) next e2
    | Econstr_stru (id, fields) ->
        let next, dest = get_dest next in
        let sfields = (get_struct_def id.id).sfields in
        let next, locals =
          List.fold_left_map (fun next (_, typ) -> scoped_tmp typ next) next sfields
        in
        let next = emit @@ Iassign (dest, RVmake (id.id, locals), next) in
        List.fold_right
          (fun (id, e) next ->
            let idx = List.find_index (fun (ids, _) -> ids.id = id.id) sfields in
            let idx = Option.get idx in
            translate_expr env (Some (PlLocal (List.nth locals idx))) next e)
          fields next
    | Ecall (id, params) ->
        let next, dest = get_dest next in
        let fformals = (get_fun_def id.id).fformals in
        let next, locals =
          List.fold_left_map (fun next (_, _, typ) -> scoped_tmp typ next) next fformals
        in
        let next = emit @@ Icall (id.id, locals, dest, next) in
        List.fold_right2
          (fun local param next -> translate_expr env (Some (PlLocal local)) next param)
          locals params next
    | Eif (c, e1, e2) ->
        let next, l = scoped_tmp Tbool next in
        let ifalse = translate_expr env dest next e2 in
        let itrue = translate_expr env dest next e1 in
        let next = emit @@ Iif (l, itrue, ifalse) in
        translate_expr env (Some (PlLocal l)) next c
    | Eloop e ->
        let brk = Some (return_unit ()) in
        let tail, rtail = fresh_instr_ref () in
        let head = translate_expr { env with brk } None tail e in
        rtail := Some (Igoto head, expr.eloc);
        head
    | Ewhile (c, e) ->
        let brk = Some (return_unit ()) in
        let tail, rtail = fresh_instr_ref () in
        let next, l = scoped_tmp Tbool tail in
        let next = translate_expr { env with brk } None next e in
        let next = emit @@ Iif (l, next, Option.get brk) in
        let head = translate_expr env (Some (PlLocal l)) next c in
        rtail := Some (Igoto head, expr.eloc);
        head
    | Ereturn None ->
        let next = emit @@ Ireturn in
        emit @@ Iassign (PlLocal Lret, RVunit, next)
    | Ereturn (Some e) ->
        let next = emit @@ Ireturn in
        translate_expr env (Some (PlLocal Lret)) next e
    | Ebreak -> emit @@ Igoto (Option.get env.brk)
    | Elet (x, _, typ, e, b) -> (
        let next, xl = scoped_tmp typ next in
        let next =
          translate_block { env with locals = SMap.add x.id xl env.locals } dest next b
        in
        match e with
        | Some e -> translate_expr env (Some (PlLocal xl)) next e
        | None -> next)
    | Eblock b -> translate_block env dest next b
  and translate_block env dest next (el, e) =
    let next = translate_expr env dest next e in
    List.fold_right (fun ei next -> translate_expr env None next ei) el next
  in

  let env =
    {
      locals =
        List.fold_left
          (fun locals (id, _, _) -> SMap.add id.id (Lparam id.id) locals)
          SMap.empty fd.fformals;
      brk = None;
    }
  in
  let next = emit fd.fbody.eloc @@ Ireturn in
  let mentry = translate_expr env (Some (PlLocal Lret)) next fd.fbody in

  let moutlives_graph = all_outlives_fn fd in
  let minstrs = Array.of_seq @@ Seq.map (fun i -> Option.get !i) @@ Queue.to_seq instrs in
  { mgeneric_lfts = fd.flfts; moutlives_graph; mlocals; mentry; minstrs; mloc = fd.floc }

(* Reverse MIR code, because we are building it backwards, which makes it hard to read. *)
let reverse_mir body =
  let revid =
    let n = Array.length body.minstrs - 1 in
    fun id -> n - id
  in
  let mentry = revid body.mentry in
  let trans_instr (instr, loc) =
    match instr with
    | Iassign (pl, rv, id) -> Iassign (pl, rv, revid id), loc
    | Ideinit (l, id) -> Ideinit (l, revid id), loc
    | Igoto id -> Igoto (revid id), loc
    | Iif (c, id1, id2) -> Iif (c, revid id1, revid id2), loc
    | Ireturn -> Ireturn, loc
    | Icall (f, lcls, pl, id) -> Icall (f, lcls, pl, revid id), loc
  in
  let minstrs = Array.of_list @@ List.rev_map trans_instr @@ Array.to_list body.minstrs in
  { body with minstrs; mentry }

let emit_fun fd = reverse_mir @@ emit_fun fd
