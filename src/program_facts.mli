(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What analysing a unit's structure observed about the program: facts, and
    no backend decisions -- those are {!Target_plan}'s.

    Computed by {!analyze} as a value, from the structure alone, before
    anything is rendered; {!Install_legacy_plan} then fills the tables
    unconverted readers consult. *)

type t = {
  used_customs : Ref.User.Set.t;
      (** The custom-extracted references the structure names -- a
          constructor's inductive with it -- whose imports its header
          includes, with those of any further custom emitting them names. *)
  higher_order_projections : Ref.User.Set.t;
      (** The projections used as function values rather than as field
          accessors, which need a standalone definition. *)
  effects : Core_effects.t;
      (** Which applications are a monad's [bind] or [ret], and the mode
          each is generated in. *)
}

val analyze : Miniml.ml_structure -> t

(** What analysing the whole frozen program observed, before it is split into
    units: interprocedural summaries, fixed points over every function. *)
type program = {
  throwing_values : Names.GlobRef.t list;
      (** The definitions whose body only throws. *)
  parameter_ownership : (Names.GlobRef.t * bool list) list;
      (** Which parameters of each function it owns rather than borrows,
          innermost first ({!Ownership.summarize}). *)
  recursive_groups : Recursive_groups.t;
      (** Which functions recurse through which. *)
}

(** [analyze_program p] analyses the frozen program [p]; it writes nothing. *)
val analyze_program : Core.frozen Core.program -> program
val equal : t -> t -> bool
