(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What every stage of one unit's extraction reads about the unit: a value
    built where the unit starts, once its plan decides its configuration,
    and handed to the stages that generate, finish and render it.  Lowering
    finds it in its input ({!Translation_state.unit_context}), naming and
    printing in the position they write at ({!Cpp_state.render_ctx}), the
    finishing passes in their argument ({!Cpp_pipeline.finish}).  Nothing
    installs it anywhere for a reader to find. *)

(** The standard library names a unit's files are written with: each the
    [std::] or [bsl::] spelling of the field's name unless noted; [Crane
    NonAtomicRc], [Crane FastVariant], [Crane SharedVariant] and
    [CRANE_COUNT_RC] substitute runtime names ([Cpp_state.std_names_of]). *)
type std_names = {
  shared_ptr : string;  (** the smart pointer for recursive fields *)
  make_shared : string;  (** its factory *)
  move : string;
  forward : string;
  logic_error : string;
  ns : string;  (** the bare namespace, ["std"] or ["bsl"] *)
  string : string;  (** the string class a spliced literal is constructed as *)
  same_as : string;  (** unqualified in the BDE flavor *)
  declval : string;
  convertible_to : string;  (** unqualified in the BDE flavor *)
  holds_alternative : string;
  get_if : string;
  get : string;
  variant : string;  (** the tagged union inductives store alternatives in *)
  variant_header : Table.header;  (** the header declaring {!variant} *)
  enable_from_this : string;  (** the base a type that hands out pointers to itself derives from *)
}

(** The plain [std::] flavor of {!std_names}. *)
val default_std_names : std_names

type t = {
  config : Table.unit_config;
      (** The unit's configuration ({!Target_plan.t.config}): whether it
          runs on several threads, which withholds a [Crane NonAtomicRc] or
          [Crane SingleThreaded] request. *)
  callables : Callable_abi.decided;
      (** The callable plans decided so far: none until the unit's are
          ({!Callable_abi.decide}), then its own, its foreign and its
          projection plans as they are planned. *)
  modules : Module_plan.layout;
      (** Where each declaration lives and what it is called: the layout
          the earlier units of the extraction decided, and the unit's own
          as its planning extends it ({!Accumulated_plan.context}). *)
  pointer_fields : Pointer_fields.t;
      (** The fields each constructor struct stores behind the pointer, as
          the earlier units and the unit's own planning decided them. *)
  unmerged_wrappers : Names.ModPath.t CString.Map.t;
      (** The wrapper structs that hold declarations, and so are not merged
          with their eponymous inductive's struct, by name, with the module
          each wraps. *)
  accessors : Struct_plan.accessors;
      (** The constants written as accessor functions. *)
  nested_structs : Struct_plan.nested_structs;
      (** The structs written inside another struct, by name. *)
  promoted_inductives : Ref.User.Set.t;
      (** The inductives promoted into their own namespace struct (e.g.
          String.string -> [namespace String { struct String }]): the
          unit's, planned ([Cpp.plan_promoted_inductives]), and every
          earlier unit's of a separate extraction, since a promotion
          outlives the unit that decided it. *)
  instance_promoted_types : (Names.Id.t * Core.Type.t) list Names.GlobRef.Map.t;
      (** The concrete types each instance gives its class's promoted
          variables: those of the unit's instances, planned
          ([Cpp.plan_instance_promoted_types]), and of every earlier
          unit's. *)
  scopes : Scope_plan.bound;
      (** How a definition written outside its struct's body names the
          struct, and the other facts of the unit's scope plan: none until
          the plan is decided ({!Cpp.plan_scopes}). *)
  names : Name_resolution.t option;
      (** How each inductive of the unit is classified -- enum, record,
          eponymous record ({!Name_resolution}) --, decided where the
          structure is analysed ([Cpp.prepare_structure]); none before
          that, where readers fall back on the table. *)
  loops : Loop_facts.t;
      (** What loop lowering reads of the analysis of the program and of
          the unit: how each function recurses, the loops it lowers to, and
          the unit's effect operations; those of a program that defines
          nothing until the unit is analysed. *)
  std_names : std_names;
      (** The standard library names the unit's files are written with, as
          its configuration and the table's settings decide them
          ([Cpp_state.with_std_names]); the plain [std::] flavor until the
          unit is configured. *)
}

(** [make ~config] is the context of a unit configured as [config], with
    no plan decided. *)
val make : config:Table.unit_config -> t

(** The context of a declaration extracted outside every unit: one that
    runs on one thread. *)
val detached : t

(** {!Table.non_atomic_rc_for} the unit's configuration. *)
val non_atomic_rc : t -> bool

(** {!Table.count_rc_for} the unit's configuration. *)
val count_rc : t -> bool

(** Whether the inductive is promoted in the unit
    ({!t.promoted_inductives}). *)
val is_promoted_inductive : t -> Names.GlobRef.t -> bool

(** The concrete types the instance gives its class's promoted variables
    in the unit ({!t.instance_promoted_types}); none where it gives none. *)
val instance_promoted_types_of : t -> Names.GlobRef.t -> (Names.Id.t * Core.Type.t) list

(** The program's recursion plan ({!t.loops}). *)
val recursion : t -> Recursion_plan.t

(** The program's loops ({!t.loops}). *)
val control : t -> Lower_control.t

(** The unit's effect operations, as loop lowering reads them ({!t.loops}). *)
val loop_effects : t -> Core_effects.t
