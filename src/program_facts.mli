(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What preparing a structure decided about its layout, before anything is
    rendered: where declarations live and what they are called.  Installed
    by {!Cpp.prepare_structure}, the one writer, and read-only afterwards --
    which is what makes it safe to read from a [.cpp] body printed before the
    [.h] that declares the names. *)

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
  functor_app_sources : (ModPath.t * ModPath.t) list;
      (** The functor body each functor application's declarations are
          copies of. *)
  eponymous_records : GlobRef.t list;
      (** Records merged into the module struct of the same name. *)
  namespace_scope_refs : GlobRef.t list;
      (** Declarations lifted out of their wrapper struct to namespace scope. *)
  wrappers : (ModPath.t * string * wrapper_role option) list;
      (** Modules emitted inside a wrapper struct, with its name and their
          role; a role not given keeps the one already recorded, and is [Own]
          otherwise. *)
  global_scope_types : GlobRef.t list;
      (** Type names a wrapper's module contributes to global scope rather
          than to the struct: its aliases and its lifted instances. *)
}

(** Record a unit's facts.  The enums replace the previous unit's; the rest
    accumulate over the extraction, the namespace-scope refs over the unit. *)
val install : t -> unit

val is_global_scope_enum : GlobRef.t -> bool
val concept_name : GlobRef.t -> string option
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
