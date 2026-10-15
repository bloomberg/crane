(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What the backend decided about a unit before rendering it: policy, read
    from the structure and its {!Program_facts}, as a value.

    Transitional: the plan holds the decisions converted so far -- the kinds
    inductives are emitted as, the kinds of their template parameters, the
    layout, the names of the globals the unit declares and of their
    constructors' fields, which of those fields are stored behind the
    pointer, and the callable plan of every generated function and method.
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

(** How the unit's declarations are spelled and stored, decided once its
    layout is ({!with_layout}). *)
type representation = {
  module_names : (Names.ModPath.t * string) list;
      (** The C++ name of each module the unit declares, in declaration
          order. *)
  names : (Names.GlobRef.t * string) list;
      (** The C++ name of each global the unit declares, in declaration
          order. *)
  referenced_names : (Names.GlobRef.t * string) list;
      (** The C++ name of each other global the unit refers to, in the order
          a walk of the structure meets them. *)
  field_names : (Names.GlobRef.t * Names.Id.t list) list;
      (** The names of each generated constructor struct's fields. *)
  pointer_fields : (Names.GlobRef.t * string * (int * bool) list) list;
      (** The fields each generated constructor struct stores behind the
          smart pointer, by inductive and constructor struct name, each with
          whether it holds the inductive itself. *)
  unmerged_wrappers : string list;
      (** The wrapper structs that hold declarations, and so are not merged
          with their eponymous inductive's struct. *)
  promoted_inductives : Names.GlobRef.t list;
      (** The inductives promoted to their eponymous module's struct. *)
  accessors : Names.GlobRef.t list;
      (** The constants emitted as accessor functions, which a use calls. *)
  nested_structs : (string * Cpp_state.nested_struct_owner) list;
      (** The structs written inside another struct, with their names. *)
  instance_promoted_types : (Names.GlobRef.t * (Names.Id.t * Miniml.ml_type) list) list;
      (** The concrete types each instance gives its class's promoted
          variables. *)
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
  representation : representation;
  callables : Callable_abi.t list;
      (** The callable plan of each function and method the unit generates,
          decided once the layout is installed ({!with_layout}). *)
  assumed_callables : (Names.GlobRef.t * Param_pos.orig Param_pos.pos list) list;
      (** For each function of the unit that has no callable plan -- a
          custom mapping's, a projection's -- the declared positions of the
          callables its call sites assume it deduces, decided with the
          callable plans. *)
}

(** [plan facts struc] decides; it writes nothing. *)
val plan : Program_facts.t -> Miniml.ml_structure -> t

(** [plan] with the template-parameter kinds decided. *)
val with_template_kinds : t -> (Names.GlobRef.t * Tparam_kinds.t) list -> t

(** [plan] with its layout, the representation of its declarations, the
    callable plans and the assumed callables decided. *)
val with_layout :
  t ->
  Module_plan.t ->
  representation ->
  Callable_abi.t list ->
  (Names.GlobRef.t * Param_pos.orig Param_pos.pos list) list ->
  t

(** The same callable plans, whatever order they were planned in. *)
val same_callables : Callable_abi.t list -> Callable_abi.t list -> bool

(** The kind decided for [block], if any. *)
val kind_of : t -> Names.MutInd.t -> Miniml.inductive_kind option

(** The same kind; a record or class by its field references. *)
val kind_equal : Miniml.inductive_kind -> Miniml.inductive_kind -> bool

(** The same decisions, the input aside. *)
val equal : t -> t -> bool
