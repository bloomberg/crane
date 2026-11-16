(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** How a unit's declarations sit in structs, as planned before anything is
    rendered and accumulated over the units of an extraction
    ({!Accumulated_plan.t}): the constants written as accessor functions,
    and the structs written inside another struct.  A unit's stages read
    them, with the unmerged wrappers, off its context ({!Unit_plan.Context.t}). *)

(** {2 Accessors} *)

(** The definitions written as function accessors (Meyers singletons)
    instead of static inline variables, to avoid template static
    initialisation order problems: by module path and label, and by the
    canonical kernel name of a constant, which is what a constant reached
    through a module alias is. *)
type accessors = {
  accessor_names : (Names.ModPath.t * Names.Label.t) list;
  accessor_constants : Names.KerName.t list;
}

(** No accessors. *)
val no_accessors : accessors

(** [a] with the definition [lbl] of [mp] an accessor. *)
val add_accessor : accessors -> Names.ModPath.t -> Names.Label.t -> accessors

(** {!add_accessor} for a global reference, which also records the
    constant's kername for cross-functor matching. *)
val add_accessor_ref : accessors -> Names.GlobRef.t -> accessors

(** Whether the constant's canonical kernel name is one of [a]'s. *)
val is_accessor_constant : accessors -> Names.Constant.t -> bool

(** Whether the definition [lbl] of [mp] is one of [a]'s. *)
val is_accessor : accessors -> Names.ModPath.t -> Names.Label.t -> bool

(** {2 Nested structs} *)

(** What a nested struct name was emitted for: a Rocq reference, or a module
    (which has no [GlobRef.t]). *)
type nested_struct_owner =
  | Global of Names.GlobRef.t
  | Module of Names.ModPath.t

(** The C++ names of the structs emitted as members of an enclosing struct,
    mapped to every owner they stand for.  One name can map to several
    owners: sibling modules may each declare a type [t]. *)
type nested_structs = nested_struct_owner list CString.Map.t

(** Equality on {!nested_struct_owner}. *)
val nested_struct_owner_equal : nested_struct_owner -> nested_struct_owner -> bool

(** Whether [owner] is the nested struct that [r] is itself emitted as,
    either because [r] is that struct or because [r] is a member of the
    module that is. *)
val nested_struct_owner_covers : Names.GlobRef.t -> nested_struct_owner -> bool

(** [m] with the owner emitted as a nested struct under the given C++
    name. *)
val add_nested_struct_name : nested_structs -> string * nested_struct_owner -> nested_structs
