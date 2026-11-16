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
    taken back to [extracted] by {!Core.Widen}.

    The other forms are shared because both phases make them.
    [Type.Unknown] is what extraction gives a type it cannot reconstruct and
    what lowering writes for an argument it erases; [Expr.Lambda_group_barrier]
    is made by extraction and again by control lowering and call lowering
    after freezing; [Type.Hole] stands in a frozen instantiation from
    extraction on; and [Type.Open], though freezing mints it, is also what
    {!Core_util.new_meta} makes when a later declaration of the same
    extraction is reconstructed after an earlier program was frozen.
    Inductives take no index: their constructor types are frozen as
    extraction stores them, so the table and the program share one frozen
    inductive. *)

(** As extraction reconstructs it: types may hold metavariables.  The
    constructor is never built: it is there so that the type checker knows
    [extracted] and [frozen] apart (two empty types it does not). *)
type extracted = Extracted_phase

(** Frozen: no metavariable is reachable. *)
type frozen = Frozen_phase

(** Evidence that a phase is [extracted], which a metavariable cell
    carries: a reader of a type of any phase that meets a cell matches it to
    learn that the phase is [extracted].  There is no [frozen is_extracted]
    value, so a [frozen] cell cannot exist. *)
type _ is_extracted = Extracted : extracted is_extracted
