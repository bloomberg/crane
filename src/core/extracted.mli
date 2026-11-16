(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What exists of Core only while types are reconstructed: the
    metavariables extraction and the Core passes make and solve.  A cell is
    made only at {!Phase.extracted}, so no frozen type holds one.  Freezing
    the program ({!Core_phase.freeze}) replaces each by its solution, or by a
    {!Core.Type.Open} where there is none, in the program and in the types its
    globals are registered at, and from then on none is made
    ({!Base.Core_util.new_meta} makes an open annotation instead) and none solved:
    under [CRANE_CHECK_IR] a solve after it is an anomaly. *)

module Meta : sig
  (** Making and solving metavariables.

      A local definition's open types are minted before freezing
      ({!Local_types}), and after it a slot that fills a hole carries the
      answer to the terms mentioning the hole instead of writing it
      ({!Base.Type_util.refine_erased}). *)

  (** A metavariable cell ({!Core.Type.Meta}): read anywhere, made and solved
      only here. *)
  type 'p cell = 'p Grammar.Meta.t = private {
    id : int;
    mutable contents : 'p Type.at option;
    phase : 'p Phase.is_extracted;  (** what makes a frozen cell impossible *)
  }

  (** A cell of the extracted program, the only phase that has one: a
      [_ cell] value is evidence that its phase is [Phase.extracted]. *)
  type t = Phase.extracted cell

  (** An unsolved cell numbered [id]. *)
  val fresh : int -> t

  (** [fresh_like m id] is an unsolved cell numbered [id] of [m]'s phase:
      a cell exists only at [Phase.extracted], so a reader of a type of any
      phase that meets one may make another for the same type. *)
  val fresh_like : 'p cell -> int -> 'p cell

  (** [cast m t] is the extracted type [t] at [m]'s phase, which is
      [Phase.extracted] since [m] exists. *)
  val cast : 'p cell -> Type.extracted -> 'p Type.at

  (** A cell numbered [id], already solved to [t]. *)
  val solved : int -> Type.extracted -> t

  (** [solve m t] fills [m] with [t]; an anomaly under [CRANE_CHECK_IR]
      after {!freeze}. *)
  val solve : 'p cell -> 'p Type.at -> unit

  (** From here nothing solves a metavariable. *)
  val freeze : unit -> unit

  (** Solves are allowed again, as at the start of an extraction. *)
  val thaw : unit -> unit

  (** Whether {!freeze} has run since the last {!thaw}. *)
  val is_frozen : unit -> bool
end
