(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The module plan: what preparing a structure decided about its layout,
    before anything is rendered -- where declarations live and what they are
    called.  These are backend decisions, part of a unit's target plan
    ({!Driver.Target_plan.t.modules}), not observations about the program.  Decided by
    {!Emit.Files.prepare_structure} and completed by
    {!Emit.Files.plan_concept_prerequisites}; each decision is folded into the
    layout the extraction has accumulated ({!extend}, the [modules] field of
    {!Driver.Accumulated_plan.t}) and handed to the unit's stages in its context
    ({!Unit_plan.Context.t.modules}) before anything is rendered, read-only
    afterwards -- which is what makes it safe to read from a [.cpp] body
    printed before the [.h] that declares the names. *)

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

(** A record merged into the module struct of the same name, and how many
    type parameters that struct is a template over. *)
type eponymous_record = {record : GlobRef.t; type_params : int}

(** Where the concepts of the module types a module declares are declared.
    A concept cannot be declared inside the class template a functor
    becomes, so those of a functor's body are declared at the file scope of
    the functor, named after it ([functor_]) and over its parameters
    ([args]) as well as the module they constrain; an application of the
    functor declares none of its own, its module types being the functor's
    concepts over the application's arguments. *)
type concept_scope = {functor_ : ModPath.t; args : ModPath.t list}

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
  eponymous_records : eponymous_record list;
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
          ({!Emit.Files.plan_concept_prerequisites}). *)
}

(** The plan of a unit that decides nothing. *)
val empty : t

(** Field-by-field equality, lists compared in order. *)
val equal : t -> t -> bool

(** The layout the queries below read: the facts of every plan a unit and
    the earlier units of its extraction decided, as {!extend} folds them. *)
type layout

(** No facts. *)
val no_layout : layout

(** [extend l t] is [l] with the facts of [t].  The enums replace those of
    [l]; the rest accumulate, the answer [t] gives about a name replacing
    the one [l] gave, and a wrapper's role not given keeping the one [l]
    recorded. *)
val extend : layout -> t -> layout

(** What a separate extraction's next unit starts from: [l] without the
    facts that belong to one unit, the namespace-scope refs and the concept
    prerequisites. *)
val for_next_unit : layout -> layout

(** {1 Queries}

    Each reads the layout it is handed: the one a unit is planned and
    rendered with is in its context ({!Unit_plan.Context.t.modules}). *)

(** Whether an enum inductive is written at global scope
    ([global_scope_enums] of the current unit). *)
val is_global_scope_enum : layout -> GlobRef.t -> bool

(** The name a type class's concept is emitted under, if planned. *)
val concept_name : layout -> GlobRef.t -> string option

(** The name a module type's concept is emitted under, if planned. *)
val modtype_concept_name : layout -> ModPath.t -> string option

(** The functor body a functor application's declarations are copies of. *)
val functor_app_source : layout -> ModPath.t -> ModPath.t option

(** Whether an inductive is a record merged into its module's struct. *)
val is_eponymous_record : layout -> GlobRef.t -> bool

(** The eponymous record of the module a constant is declared in, if any: at
    most one record shares its module's name.  A function there is spelled
    [Record<Args>::f()]. *)
val eponymous_record_containing : layout -> GlobRef.t -> eponymous_record option

(** Whether a declaration is lifted out of its wrapper to namespace scope in
    the current unit. *)
val is_namespace_scope_ref : layout -> GlobRef.t -> bool

(** The wrapper struct a module is emitted in, and its role there. *)
val wrapper : layout -> ModPath.t -> (string * wrapper_role) option

(** The name of {!wrapper}. *)
val wrapper_struct : layout -> ModPath.t -> string option

(** The role of {!wrapper}. *)
val wrapper_role : layout -> ModPath.t -> wrapper_role option

(** Whether a type name goes to global scope rather than its wrapper's
    struct. *)
val is_global_scope_type : layout -> GlobRef.t -> bool

(** Whether a top-level element of the current unit moves ahead of the
    header's concepts. *)
val is_concept_prerequisite : layout -> Label.t -> bool
