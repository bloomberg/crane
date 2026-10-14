(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What the backend decided about a unit before rendering it: policy, read
    from the structure and its {!Program_facts}, as a value.

    Transitional: the plan holds the decisions converted so far -- the kinds
    inductives are emitted as.  The layout is still the {!Module_plan}
    discovery's [prepare] installs, and template-parameter kinds are still
    recorded by {!Cpp_ind.plan_template_kinds}; both belong here.
    {!Install_legacy_plan} fills the tables unconverted readers consult. *)

(** Why an inductive is emitted as a kind other than the one extraction
    classified it as. *)
type kind_reason =
  | Functor_alignment
      (** A functor application's copy takes the kind the functor body's own
          copy has, which is the one emitted. *)
  | Used_as_value
      (** A type class the structure handles as data is a struct, not a
          concept. *)

type kind_decision = {
  block : Names.MutInd.t;
  kind : Miniml.inductive_kind;
  reason : kind_reason;
}

type t = {
  input : Ml_fingerprint.t option;
      (** The structure planned, where something reads it: under
          [CRANE_CHECK_IR] or [CRANE_TRACE_PIPELINE]. *)
  inductive_kinds : kind_decision list;
      (** In the order they were decided; a later decision about a block
          supersedes an earlier one. *)
}

(** [plan facts struc] decides; it writes nothing. *)
val plan : Program_facts.t -> Miniml.ml_structure -> t

(** The kind decided for [block], if any. *)
val kind_of : t -> Names.MutInd.t -> Miniml.inductive_kind option

(** The same kind; a record or class by its field references. *)
val kind_equal : Miniml.inductive_kind -> Miniml.inductive_kind -> bool

(** The same decisions, the input aside. *)
val equal : t -> t -> bool
