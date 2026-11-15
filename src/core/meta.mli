(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Making and solving metavariables.

    A metavariable is extraction's: unification solves it while types are
    reconstructed, and the Core passes may still.  Freezing the program
    ({!Core_phase.freeze}) replaces each by its solution, or by a
    {!Type.Open} where there is none, and from then on none is made
    ({!Mlutil.new_meta} makes an open annotation instead) and none solved: a
    local definition's open types are minted before it ({!Local_types}), and
    a slot that fills a hole carries the answer to the terms mentioning the
    hole instead of writing it ({!Ml_type_util.refine_erased}).  Under
    [CRANE_CHECK_IR] a solve after freezing is an anomaly. *)

(** A metavariable cell ({!Grammar.Meta}): read anywhere, made and solved
    only here. *)
type t = Grammar.Meta.t = private {
  id : int;
  mutable contents : Type.t option;
}

val fresh : int -> t

(** A cell numbered [id], already solved to [t]. *)
val solved : int -> Type.t -> t

val solve : t -> Type.t -> unit

(** From here nothing solves a metavariable. *)
val freeze : unit -> unit

(** Solves are allowed again, as at the start of an extraction. *)
val thaw : unit -> unit

(** Whether {!freeze} has run since the last {!thaw}. *)
val is_frozen : unit -> bool
