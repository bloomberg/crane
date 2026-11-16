(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

module Meta = struct
  type 'p cell = 'p Grammar.Meta.t = private {
    id : int;
    mutable contents : 'p Type.at option;
  }

  type t = Phase.frozen cell

  let fresh id = Grammar.Meta.make id None
  let solved id t = Grammar.Meta.make id (Some t)
  let frozen = ref false

  let solve m t =
    if !frozen && Sys.getenv_opt "CRANE_CHECK_IR" <> None then
      CErrors.anomaly Pp.(str "Crane: a metavariable of the frozen program was solved.");
    Grammar.Meta.set m t

  let freeze () = frozen := true
  let thaw () = frozen := false
  let is_frozen () = !frozen
end
