(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

type t = Grammar.Meta.t = {
  id : int;
  mutable contents : Type.t option;
}

let fresh id = {id; contents = None}
let solved id t = {id; contents = Some t}
let frozen = ref false

let solve m t =
  if !frozen && Sys.getenv_opt "CRANE_CHECK_IR" <> None then
    CErrors.anomaly Pp.(str "Crane: a metavariable of the frozen program was solved.");
  m.contents <- Some t

let freeze () = frozen := true
let thaw () = frozen := false
let is_frozen () = !frozen
