(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The phase index of Core's grammar: every family that holds a type takes
    one ([_ Core.Type.at], [_ Core.Expr.at], ...), and each family's [t] is
    its [frozen] instance, the one every consumer after
    {!Core_phase.freeze} reads.

    What tells the two apart is the metavariable: a {!Core.Type.Meta} holds
    a cell of its own phase, and only an [extracted] cell can be made
    ({!Core.Extracted.Meta}), so a [frozen] term holds none.  Freezing is
    the one conversion from [extracted] to [frozen]; a [frozen] term is
    taken back to [extracted] by {!Core.Type.widen} and
    {!Core.Expr.widen}. *)

(** As extraction reconstructs it: types may hold metavariables. *)
type extracted = Extracted

(** Frozen: no metavariable is reachable. *)
type frozen = Frozen
