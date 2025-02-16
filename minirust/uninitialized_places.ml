(* Once you are done writing the code, remove this directive,
   whose purpose is to disable several warnings. *)
[@@@warning "-26-27-33"]

(* You should read and understand active_borrows.ml *fully*, before filling the holes
  in this file. The analysis in this file follows the same structure. *)

open Type
open Minimir

type analysis_results = label -> PlaceSet.t

let go mir : analysis_results =
  (* The set of all places appearing in the MIR code. We are not interested in initializedness for places
    which are not members of this set. *)
  let local_places =
    Hashtbl.fold
      (fun l _ acc -> PlaceSet.add (PlLocal l) acc)
      mir.mlocals PlaceSet.empty
  in

  let all_places =
    Array.fold_left
      (fun acc (i, _) ->
        match i with
        | Ideinit _ | Iif _ | Igoto _ | Ireturn -> acc
        | Icall (_, _, pl, _) -> PlaceSet.add pl acc
        | Iassign (pl, rv, _) -> (
            let acc = PlaceSet.add pl acc in
            match rv with
            | RVplace pl | RVborrow (_, pl) -> PlaceSet.add pl acc
            | RVbinop _ | RVunop _ | RVmake _ | RVunit | RVconst _ -> acc))
      local_places mir.minstrs
  in

  (* The set of subplaces of a given place. *)
  let subplaces = Hashtbl.create 7 in
  let () =
    PlaceSet.iter
      (fun pl ->
        let pls = PlaceSet.filter (fun pl_sub -> is_subplace pl_sub pl) all_places in
        Hashtbl.add subplaces pl pls)
      all_places
  in

  (* Effect of initializing a place [pl] on the abstract state [state]: [pl] and all its subplaces
    become initialized. Hence, given that the state is the set of uninitialized places, we remove
    the subplaces [pl] from the abstract state. *)
  let initialize pl state = PlaceSet.diff state (Hashtbl.find subplaces pl) in

  (* This is the dual: we are consuming or deinitiailizing place [pl], so all its subplaces
    become uninitialized, so they are added to [state]. *)
  let deinitialize pl state = PlaceSet.union state (Hashtbl.find subplaces pl) in

  (* Effect of using (copying or moving) a place [pl] on the abstract state [state]. *)
  let move_or_copy pl state = if typ_is_copy (typ_of_place mir pl) then state else PlaceSet.union state (Hashtbl.find subplaces pl) in

  (* These modules are parameters of the [Fix.DataFlow.ForIntSegment] functor below. *)
  let module Instrs = struct let n = Array.length mir.minstrs end in
  let module Prop = struct
    type property = PlaceSet.t

    let leq_join p q = if PlaceSet.subset p q then q else PlaceSet.union p q
  end in
  let module Graph = struct
     type variable = int
    type property = PlaceSet.t

    (* To complete this module, one can read file active_borrows.ml, which contains a
      similar data flow analysis. *)

    let foreach_root go =
      go mir.mentry (PlaceSet.fold initialize local_places all_places) (* DONE *)

    let foreach_successor lbl state go =
      match fst mir.minstrs.(lbl) with
      | Iassign (pl, v, next) ->
        let state =
          match v with
          | RVplace pl1 -> move_or_copy pl1 state
          | RVborrow (_, pl1) -> move_or_copy pl1 state
          | RVbinop (_, l1, l2) -> move_or_copy (PlLocal l2) (move_or_copy (PlLocal l1) state)
          | RVunop (_, l1) -> move_or_copy (PlLocal l1) state
          | RVmake (_, l) -> List.fold_left (fun state l ->  move_or_copy (PlLocal l) state) state l
          | _ -> state
        in go next (initialize pl state)
      | Ideinit (l, next) -> go next (deinitialize (PlLocal l) state)
      | Igoto next -> go next state
      | Iif (l, next1, next2) ->
          let state = deinitialize (PlLocal l) state in
          go next1 state;
          go next2 state
      | Ireturn -> ()
      | Icall (_, args, pl, next) -> go next (initialize pl (List.fold_left (fun state l -> deinitialize (PlLocal l) state) state args)) (* DONE *)
  end in
  let module Fix = Fix.DataFlow.ForIntSegment (Instrs) (Prop) (Graph) in
  fun i -> Option.value (Fix.solution i) ~default:PlaceSet.empty
