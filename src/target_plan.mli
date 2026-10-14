(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What the backend decided about a unit before rendering it: policy, read
    from the structure and its {!Program_facts}, as a value.

    Transitional: the plan holds the decisions converted so far -- the kinds
    inductives are emitted as, the kinds of their template parameters, the
    layout, and every generated function's callable plan.
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
  template_kinds : (Names.GlobRef.t * Tparam_kinds.t) list;
      (** The kinds of the template parameters of each inductive and type
          alias the unit generates, decided once the inductive kinds are
          installed ({!with_template_kinds}). *)
  modules : Module_plan.t;
      (** Where each declaration lives and what it is called, decided once
          the template-parameter kinds are installed ({!with_layout}). *)
  callables : Callable_abi.t list;
      (** The callable plan of each function the unit generates, decided once
          the layout is installed ({!with_layout}). *)
}

(** [plan facts struc] decides; it writes nothing. *)
val plan : Program_facts.t -> Miniml.ml_structure -> t

(** [plan] with the template-parameter kinds decided. *)
val with_template_kinds : t -> (Names.GlobRef.t * Tparam_kinds.t) list -> t

(** [plan] with its layout and the callable plans decided. *)
val with_layout : t -> Module_plan.t -> Callable_abi.t list -> t

(** The same callable plans, whatever order they were planned in. *)
val same_callables : Callable_abi.t list -> Callable_abi.t list -> bool

(** The kind decided for [block], if any. *)
val kind_of : t -> Names.MutInd.t -> Miniml.inductive_kind option

(** The same kind; a record or class by its field references. *)
val kind_equal : Miniml.inductive_kind -> Miniml.inductive_kind -> bool

(** The same decisions, the input aside. *)
val equal : t -> t -> bool
