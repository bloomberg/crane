(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The module plan: what preparing a structure decided about its layout,
    before anything is rendered -- where declarations live and what they are
    called.  These are backend decisions, part of a unit's target plan
    ({!Target_plan.modules}), not observations about the program.  Decided by
    {!Cpp.prepare_structure} and installed by {!Install_legacy_plan}, the one
    writer, before anything is rendered, and read-only afterwards -- which is
    what makes it safe to read from a [.cpp] body printed before the [.h] that
    declares the names. *)

open Names

(** How a module sits in the wrapper struct it is emitted in. *)
type wrapper_role =
  | Own  (** The wrapper is the module's own struct. *)
  | Flattened
      (** A child whose name collides with a global inductive, flattened into
          its parent's struct: its qualifier is stripped. *)
  | Bystander
      (** A child a collision wrapper absorbed without a collision of its own:
          it keeps its own nesting, so the wrapper's name goes in front of its
          own rather than in place of it. *)

(** The facts one unit's preparation decided. *)
type t = {
  global_scope_enums : GlobRef.t list;
      (** Enum inductives written at global scope, not inside a struct. *)
  concept_names : (GlobRef.t * string) list;
      (** The name a type class's concept is emitted under, where the class's
          own name does not settle it. *)
  modtype_concept_names : (ModPath.t * string) list;
      (** The same for a module type's concept. *)
  functor_app_sources : (ModPath.t * ModPath.t) list;
      (** The functor body each functor application's declarations are
          copies of. *)
  eponymous_records : GlobRef.t list;
      (** Records merged into the module struct of the same name. *)
  namespace_scope_refs : GlobRef.t list;
      (** Declarations lifted out of their wrapper struct to namespace scope:
          instances, and the inductives a collision struct holds that are
          concept prerequisites. *)
  wrappers : (ModPath.t * string * wrapper_role option) list;
      (** Modules emitted inside a wrapper struct, with its name and their
          role; a role not given keeps the one already recorded, and is [Own]
          otherwise. *)
  global_scope_types : GlobRef.t list;
      (** Type names a wrapper's module contributes to global scope rather
          than to the struct: its aliases and its lifted instances. *)
  concept_prerequisites : Label.t list;
      (** The labels of the files' top-level elements the concepts at the top
          of the header cannot be read without, which move ahead of them
          ({!Cpp.plan_concept_prerequisites}). *)
}

(** The plan of a unit that decides nothing. *)
val empty : t

val equal : t -> t -> bool

(** Record a unit's facts.  The enums replace the previous unit's; the rest
    accumulate over the extraction, the namespace-scope refs and the concept
    prerequisites over the unit.  Recording a plan again records nothing
    new but what it adds. *)
val install : t -> unit

(** Whether every decision of [t] reads back as {!install} recorded it: the
    last answer [t] gives about a name, and a wrapper's role where [t] gives
    one. *)
val installed : t -> bool

val is_global_scope_enum : GlobRef.t -> bool
val concept_name : GlobRef.t -> string option
val modtype_concept_name : ModPath.t -> string option
val functor_app_source : ModPath.t -> ModPath.t option
val is_eponymous_record : GlobRef.t -> bool

(** The eponymous record of the module a constant is declared in, if any: at
    most one record shares its module's name.  A function there is spelled
    [Record<Args>::f()]. *)
val eponymous_record_containing : GlobRef.t -> GlobRef.t option

val is_namespace_scope_ref : GlobRef.t -> bool
val wrapper : ModPath.t -> (string * wrapper_role) option
val wrapper_struct : ModPath.t -> string option
val wrapper_role : ModPath.t -> wrapper_role option
val is_global_scope_type : GlobRef.t -> bool
val is_concept_prerequisite : Label.t -> bool
