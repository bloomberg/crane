(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The bridge from a unit's {!Program_facts} and {!Target_plan} to the tables
    the readers not yet converted consult: filled once, from the values,
    before anything is rendered. *)

(** [install struc facts plan] fills the legacy tables, and writes each
    decided inductive kind into the structure's declarations of that block,
    which most readers still take the kind from. *)
val install : Miniml.ml_structure -> Program_facts.t -> Target_plan.t -> unit

(** [install_program facts] fills the tables a whole program's analysis
    stands for: the throwing values and the parameter ownership. *)
val install_program : Program_facts.program -> unit

(** [install_template_kinds plan] records the template-parameter kinds [plan]
    decided, which the inductive kinds {!install} wrote went into deciding. *)
val install_template_kinds : Target_plan.t -> unit

(** [install_modules modules] records the layout, as
    {!Target_plan.modules} holds it. *)
val install_modules : Module_plan.t -> unit

(** [install_pointer_fields fields] installs the constructor structs'
    pointer fields, as {!Target_plan.representation} holds them, for the
    loop transformations to read. *)
val install_pointer_fields : (Names.GlobRef.t * string * (int * bool) list) list -> unit

(** [install_accessors constants] installs the constants emitted as accessor
    functions, as {!Target_plan.representation} holds them. *)
val install_accessors : Names.GlobRef.t list -> unit

(** [install_nested_structs structs] installs the structs written inside
    another struct, as {!Target_plan.representation} holds them. *)
val install_nested_structs : (string * Cpp_state.nested_struct_owner) list -> unit

(** [install_scopes scopes] installs the scopes of the modules emitted as
    structs, as {!Target_plan.representation} holds them. *)
val install_scopes : Scope_plan.t -> unit

(** [install_instance_promoted_types types] installs the concrete types the
    unit's instances give their classes' promoted variables, as
    {!Target_plan.representation} holds them. *)
val install_instance_promoted_types :
  (Names.GlobRef.t * (Names.Id.t * Miniml.ml_type) list) list -> unit

(** [install_promoted_inductives inductives] promotes the inductives, as
    {!Target_plan.representation} holds them. *)
val install_promoted_inductives : Names.GlobRef.t list -> unit

(** [install_unmerged_wrappers names] installs the wrapper structs that hold
    declarations, as {!Target_plan.representation} holds them. *)
val install_unmerged_wrappers : string list -> unit

(** [install_callables callables assumed] installs the callable plans and
    the assumed callables, as {!Target_plan.callables} and
    {!Target_plan.assumed_callables} hold them ({!Callable_abi.install}):
    from here a generated declaration only checks its head against its
    plan. *)
val install_callables :
  Callable_abi.t list -> (Names.GlobRef.t * Param_pos.orig Param_pos.pos list) list -> unit

(** [install_instance_methods planned] installs the plans of the instances'
    methods, as {!Target_plan.instance_methods} holds them
    ({!Callable_abi.install_instance_methods}). *)
val install_instance_methods : (Names.GlobRef.t * (Names.Id.t * Callable_abi.t) list) list -> unit

(** Under [CRANE_CHECK_IR], fail unless every table {!install},
    {!install_template_kinds}, {!install_modules} and {!install_callables}
    filled still answers what the values say.  A census sees an entry added; this sees one
    overwritten.  The used customs are the exception that may grow: emitting a
    custom's replacement marks it used, and the header's includes follow what
    was emitted. *)
val check_installed : Program_facts.t -> Target_plan.t -> unit
