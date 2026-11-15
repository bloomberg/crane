(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What exists of Core only while types are reconstructed: the
    metavariables extraction and the Core passes make and solve.  Freezing
    the program ({!Core_phase.freeze}) replaces each by its solution, or by a
    {!Core.Type.Open} where there is none, in the program and in the types its
    globals are registered at, and from then on none is made
    ({!Core_util.new_meta} makes an open annotation instead) and none solved.
    Under [CRANE_CHECK_IR] freezing checks that no metavariable is reachable,
    and a solve after it is an anomaly. *)

module Meta : sig
  (** Making and solving metavariables.

      A local definition's open types are minted before freezing
      ({!Local_types}), and after it a slot that fills a hole carries the
      answer to the terms mentioning the hole instead of writing it
      ({!Type_util.refine_erased}). *)

  (** A metavariable cell ({!Core.Type.Meta}): read anywhere, made and solved
      only here. *)
  type t = Grammar.Meta.t = private {
    id : int;
    mutable contents : Type.t option;
  }

  (** An unsolved cell numbered [id]. *)
  val fresh : int -> t

  (** A cell numbered [id], already solved to [t]. *)
  val solved : int -> Type.t -> t

  (** [solve m t] fills [m] with [t]; an anomaly under [CRANE_CHECK_IR]
      after {!freeze}. *)
  val solve : t -> Type.t -> unit

  (** From here nothing solves a metavariable. *)
  val freeze : unit -> unit

  (** Solves are allowed again, as at the start of an extraction. *)
  val thaw : unit -> unit

  (** Whether {!freeze} has run since the last {!thaw}. *)
  val is_frozen : unit -> bool
end
