open Minimir
module Fix = Fix.Fix.ForType (struct type t = int end) (Fix.Prop.Set (LocSet))

type analysis_results = label -> LocSet.t

let go mir : analysis_results =
  Fix.lfp (fun lbl live ->
      match fst mir.minstrs.(lbl) with
      | Iassign (pl, rv, next) -> (
          let live = live next in
          let live = match pl with PlLocal l -> LocSet.remove l live | _ -> live in
          let live =
            if contains_deref_borrow pl then LocSet.add (local_of_place pl) live else live
          in
          match rv with
          | RVplace pl | RVborrow (_, pl) -> LocSet.add (local_of_place pl) live
          | RVconst _ | RVunit -> live
          | RVbinop (_, l1, l2) -> LocSet.add l1 (LocSet.add l2 live)
          | RVunop (_, l) -> LocSet.add l live
          | RVmake (_, ls) -> LocSet.add_seq (List.to_seq ls) live)
      | Ideinit (l, next) ->
          let live = live next in
          LocSet.remove l live
      | Igoto next -> live next
      | Iif (c, lt, lf) -> LocSet.add c (LocSet.union (live lt) (live lf))
      | Ireturn -> LocSet.singleton Lret
      | Icall (_, ls, pl, next) ->
          let live = live next in
          let live = match pl with PlLocal l -> LocSet.remove l live | _ -> live in
          LocSet.add_seq (List.to_seq ls) live)
