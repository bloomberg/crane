(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What the backend decided about a unit before rendering it: policy, read
    from the structure, as a value.  Built by [Extract_env] after the unit's
    {!Program_facts} and before its bodies are lowered; of the facts,
    {!plan} reads only the customs the program names.

    The plan holds the unit's configuration, the kinds inductives are
    emitted as, the kinds of their template parameters, the layout, the
    names of the modules and globals the unit declares and refers to and of
    its constructors' fields, how those fields are stored, and the callable
    plan of every generated function and method.  It is filled in stages
    ({!plan}, {!with_template_kinds}, {!with_layout}).  Its readers do not
    ask it: the configuration is handed to the stages in the unit's
    context ({!Unit_plan.Context}), the inductive kinds are written into the structure ({!record_kinds}), and
    each layout decision is bound as it is taken, over the earlier units'
    ({!Accumulated_plan}).  Under [CRANE_CHECK_IR] the plan is what the
    emitted result is compared against once the unit is rendered. *)

(** Why an inductive is emitted as a kind other than the one extraction
    classified it as. *)
type kind_reason =
  | Functor_alignment
      (** A functor application's copy takes the kind the functor body's own
          copy has, which is the one emitted. *)
  | Used_as_value
      (** A type class the structure handles as data is a struct, not a
          concept. *)

(** One inductive block emitted as a kind other than extraction's. *)
type kind_decision = {
  block : Names.MutInd.t;  (** the mutual block, every packet of it *)
  kind : Core.Inductive.Kind.t;  (** the kind emitted *)
  reason : kind_reason;  (** why it differs from extraction's *)
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
  pointer_fields : (Names.GlobRef.t * string * Core_plan.Pointer_fields.planned list) list;
      (** The fields each generated constructor struct stores behind the
          smart pointer, by inductive and constructor struct name, each with
          whether it holds the inductive itself. *)
  unmerged_wrappers : (string * Names.ModPath.t) list;
      (** The wrapper structs that hold declarations, and so are not merged
          with their eponymous inductive's struct, each with the module it
          wraps. *)
  promoted_inductives : Names.GlobRef.t list;
      (** The inductives promoted to their eponymous module's struct. *)
  accessors : Names.GlobRef.t list;
      (** The constants emitted as accessor functions, which a use calls. *)
  nested_structs : (string * Unit_plan.Cpp_state.nested_struct_owner) list;
      (** The structs written inside another struct, with their names. *)
  scopes : Core_plan.Scope_plan.t;
      (** How a definition written outside its struct's body names the
          struct, for each module emitted as one, and which modules are
          written inside a struct's body. *)
  instance_promoted_types : (Names.GlobRef.t * (Names.Id.t * Core.Type.t) list) list;
      (** The concrete types each instance gives its class's promoted
          variables. *)
}

(** A unit's plan.  {!plan} fills [input], [config] and
    [inductive_kinds]; the later fields start empty and are filled by
    {!with_template_kinds} and {!with_layout} as each stage is decided. *)
type t = {
  input : Core.Fingerprint.t option;
      (** The structure planned, where something reads it: under
          [CRANE_CHECK_IR] or [CRANE_TRACE_PIPELINE]. *)
  config : Base.Table.unit_config;
      (** The unit's configuration, from the customs its program names:
          whether it runs on several threads, which withholds a [Crane
          NonAtomicRc] or [Crane SingleThreaded] request.  Generation, the
          finishing passes, the printer and the runtime's spelling read it
          off the unit's context ({!Unit_plan.Context.t.config}). *)
  inductive_kinds : kind_decision list;
      (** In the order they were decided; a later decision about a block
          supersedes an earlier one. *)
  template_kinds : (Names.GlobRef.t * Cpp_ir.Tparam_kinds.t) list;
      (** The kinds of the template parameters of each inductive and type
          alias the unit generates, decided once the inductive kinds are
          recorded ({!with_template_kinds}). *)
  modules : Core_plan.Module_plan.t;
      (** Where each declaration lives and what it is called, decided once
          the template-parameter kinds are decided ({!with_layout}). *)
  representation : representation;
      (** How declarations are spelled and stored, decided with the layout
          ({!with_layout}). *)
  callables : Core_plan.Callable_abi.t list;
      (** The callable plan of each function and method the unit generates,
          decided once the layout is bound ({!with_layout}). *)
  instance_methods : (Names.GlobRef.t * (Names.Id.t * Core_plan.Callable_abi.t) list) list;
      (** The callable plan of each method of each instance's struct, by
          name, decided with the callable plans. *)
  assumed_callables : (Names.GlobRef.t * Core_plan.Param_pos.orig Core_plan.Param_pos.pos list) list;
      (** For each function of the unit that has no callable plan -- a
          custom mapping's, a projection's -- the declared positions of the
          callables its call sites assume it deduces, decided with the
          callable plans. *)
}

(** [plan facts struc] decides the unit's configuration from the customs
    [facts] says its program names, and the inductive kinds: functor
    applications' copies aligned with their functor body's
    ({!Functor_alignment}), then type classes used as data demoted to
    records ({!Used_as_value}).  It writes nothing. *)
val plan : Program_facts.t -> Core.Program.t -> t

(** [record_kinds t struc] records each kind [t] decided where an
    inductive's kind is kept: in its declaration in [struc], the frozen
    program every reader of the unit takes a declaration from, and in the
    extracted environment ({!Base.Table.inductive_kind_of}), which answers for
    an inductive another declaration -- or a later unit of a separate
    extraction -- names.  The decision is the plan's; the program records
    its result, as it records any other fact about a declaration, so no
    reader asks the plan. *)
val record_kinds : t -> Core.Program.t -> unit

(** Under [CRANE_CHECK_IR], that the extracted environment still records
    each kind [t] decided ({!record_kinds}). *)
val check_kinds_recorded : t -> unit

(** [with_template_kinds t kinds] is [t] with the template-parameter kinds
    [kinds]. *)
val with_template_kinds : t -> (Names.GlobRef.t * Cpp_ir.Tparam_kinds.t) list -> t

(** [with_layout t modules representation (callables, instance_methods)
    assumed] is [t] with its layout, the representation of its
    declarations, the callable plans and the assumed callables. *)
val with_layout :
  t ->
  Core_plan.Module_plan.t ->
  representation ->
  Core_plan.Callable_abi.t list * (Names.GlobRef.t * (Names.Id.t * Core_plan.Callable_abi.t) list) list ->
  (Names.GlobRef.t * Core_plan.Param_pos.orig Core_plan.Param_pos.pos list) list ->
  t

(** The same callable plans, whatever order they were planned in. *)
val same_callables : Core_plan.Callable_abi.t list -> Core_plan.Callable_abi.t list -> bool

(** {!same_callables} for the plans of instances' methods. *)
val same_instance_methods :
  (Names.GlobRef.t * (Names.Id.t * Core_plan.Callable_abi.t) list) list ->
  (Names.GlobRef.t * (Names.Id.t * Core_plan.Callable_abi.t) list) list ->
  bool

(** The kind decided for [block], if any. *)
val kind_of : t -> Names.MutInd.t -> Core.Inductive.Kind.t option

(** The same kind; a record or class by its field references. *)
val kind_equal : Core.Inductive.Kind.t -> Core.Inductive.Kind.t -> bool

(** The same decisions, the input aside. *)
val equal : t -> t -> bool
