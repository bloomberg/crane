(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** This module turns Coq [GlobRef.t]s and inductive references into their C++
   names and qualified paths. It provides string and [Pp.t] renderings of
   globals, field names, and inductive/enum type names, together with the
   namespace and struct qualification needed to reference them from a given
   context. It also handles translation between Rocq and C++ path spellings.
   A few small caches (such as [globref_full_path_cache]) and cached predicates
   over the name-resolution cache ([with_cache], [*_cached]) keep repeated
   lookups cheap. *)

(** {2 String and [Pp.t] renderings of globals} *)

(** Render a global to a string, using an explicit [KerName.t] key. *)
val str_global_with_key :
  Common.kind -> Names.KerName.t -> Names.GlobRef.t -> string

(** Render a global to a string. *)
val str_global : Common.kind -> Names.GlobRef.t -> string

(** Pretty-print a global, using an explicit [KerName.t] key. *)
val pp_global_with_key :
  Common.kind -> Names.KerName.t -> Names.GlobRef.t -> Pp.t

(** Pretty-print a global. *)
val pp_global : Common.kind -> Names.GlobRef.t -> Pp.t

(** Pretty-print just the (unqualified) name of a global. *)
val pp_global_name : Common.kind -> Names.GlobRef.t -> Pp.t

(** {2 Full paths and module names} *)

(** Cache mapping globals to their fully-qualified path strings. *)
val globref_full_path_cache : (Names.GlobRef.t, string) Hashtbl.t

(** The fully-qualified path string of a global. *)
val globref_full_path : Names.GlobRef.t -> string

(** Pretty-print a module path. *)
val pp_modname : Names.module_path -> Pp.t

(** {2 Inductive references} *)

(** Whether the given global is a merged inductive. *)
val is_merged_inductive : Names.GlobRef.t -> bool

(** The inductive underlying a global reference. *)
val get_ind : Names.GlobRef.t -> Names.GlobRef.t

(** The [KerName.t] of an inductive reference. *)
val kn_of_ind : Names.GlobRef.t -> Names.KerName.t

(** {2 Record and inductive field names} *)

(** Pretty-print a single field of a record/inductive at the given index. *)
val pp_one_field : Names.GlobRef.t -> int -> Names.GlobRef.t option -> Pp.t

(** Pretty-print the field selected by index from a list of field references. *)
val pp_field : Names.GlobRef.t -> Names.GlobRef.t option list -> int -> Pp.t

(** {2 Name predicates and inductive/enum naming} *)

(** Whether a string is already a qualified (namespaced) name. *)
val is_qualified_name : string -> bool

(** Whether the inductive is a record. *)
val is_record_inductive : Names.GlobRef.t -> bool

(** Whether the inductive is local. *)
val is_local_inductive : Names.GlobRef.t -> bool

(** The pretty-printed inductive name and whether it is (e.g.) local/record. *)
val inductive_name_info : Names.GlobRef.t -> Pp.t * bool

(** Whether an enum name collides with its parent's name. *)
val enum_name_collides_with_parent : Names.GlobRef.t -> bool

(** Capitalize an enum name for the given global. *)
val capitalize_enum_name : string -> Names.GlobRef.t -> string

(** Capitalize an enum's qualified name for the given global. *)
val capitalize_enum_qualified : string -> Names.GlobRef.t -> string

(** The C++ name of a promoted (inductive) constructor/type. *)
val cpp_name_of_promoted : string -> string

(** Deduplicate a repeated trailing qualifier in a qualified name. *)
val dedup_qualified_tail : ?allow_bare:bool -> string -> string

(** Pretty-print the C++ type name of an inductive. *)
val pp_inductive_type_name : Names.GlobRef.t -> Pp.t

(** The [typename] prefix required for the given qualified name. *)
val typename_prefix_for : string -> Pp.t

(** {2 Rocq / C++ path translation} *)

(** Convert a C++ path spelling to its Rocq form. *)
val cpp_to_rocq_path : string -> string

(** Convert a Rocq path spelling to its C++ form. *)
val rocq_to_cpp_path : string -> string

(** {2 Struct and namespace qualification} *)

(** Whether a global is nested inside the given struct. *)
val is_nested_in_struct : Names.GlobRef.t -> string -> bool

(** Find the qualifier reaching a common ancestor from a given path. *)
val find_ancestor_qualifier_from : string -> string -> Pp.t

(** The struct qualifier needed to reach a global from the given context. *)
val struct_qualifier_for : Names.GlobRef.t -> string -> Pp.t

val global_scope_qualifier_for : Names.GlobRef.t -> string -> Pp.t

(** Whether the global must be referenced with a global-scope qualifier. *)
val needs_global_qualifier : Names.GlobRef.t -> bool

(** {2 Name-resolution cache and cached predicates} *)

(** Run a resolver against the name-resolution cache, falling back otherwise. *)
val with_cache :
  (Name_resolution.t -> Names.GlobRef.t -> 'a) ->
  (Names.GlobRef.t -> 'a) -> Names.GlobRef.t -> 'a

(** Cached: whether the global is an eponymous record. *)
val is_eponymous_record_cached : Names.GlobRef.t -> bool

(** Cached: whether the global is a global-scope enum. *)
val is_global_scope_enum_cached : Names.GlobRef.t -> bool

(** Cached: whether the global is a merged inductive. *)
val is_merged_inductive_cached : Names.GlobRef.t -> bool

(** Cached: the C++ inductive kind of the global, if any. *)
val get_ind_kind_cached : Names.GlobRef.t -> Minicpp.cpp_ind_kind option

(** Cached: whether the global is an enum. *)
val is_enum_cached : Names.GlobRef.t -> bool

(** Cached: whether the global is a record. *)
val is_record_cached : Names.GlobRef.t -> bool

(** {2 Method receivers} *)

(** The position of the [this] argument for a method global, if any. *)
val lookup_method_this_pos : Names.GlobRef.t -> int option

(** Whether a method's receiver is passed by pointer. *)
val method_receiver_is_ptr : 'a -> bool

(** Sets of identifiers ([Names.variable]). *)
module IdSet : Set.S with type elt = Names.variable
