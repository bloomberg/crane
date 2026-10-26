(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

type t =
  | Lowered
  | Unlowered of string
  | Kept

(* Loops are told apart by {!Control_ir.Loop.equal}: a local fixpoint's by
   the physical identity of its occurrence, which hashes to nothing, so the
   unit's verdicts are a list, written only while the checks run. *)
let verdicts : (Control_ir.Loop.t * t) list ref = State.cell State.Unit []

let record l v =
  if Probe.checking () then
    verdicts := (l, v) :: List.filter (fun (l', _) -> not (Control_ir.Loop.equal l l')) !verdicts

let find l = List.find_map (fun (l', v) -> if Control_ir.Loop.equal l l' then Some v else None) !verdicts
