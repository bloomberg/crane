(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** This module turns Coq [GlobRef.t]s and inductive references into their C++
   names and qualified paths. It provides string and [Pp.t] renderings of
   globals, field names, and inductive/enum type names, together with the
   namespace and struct qualification needed to reference them from a given
   context. Cached predicates over the name-resolution cache ([with_cache],
   [*_cached]) keep repeated lookups cheap. *)

(** {2 Names of globals} *)

(** The name of a global, using an explicit [KerName.t] key: the replacement
    text of an inline custom mapping, otherwise as resolution settles it where
    the printer is. *)
val global_name_with_key :
  Common.kind -> Names.KerName.t -> Names.GlobRef.t -> Cpp_name.t

(** {!global_name_with_key} using the default key. *)
val global_name : Common.kind -> Names.GlobRef.t -> Cpp_name.t

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

(** The name a typeclass concept is declared and referenced under: its short
    name, since a concept may only appear at namespace scope and so carries no
    struct qualifier; a use in another file names that file's namespace. *)
val concept_name : Names.GlobRef.t -> Cpp_name.t

(** {!concept_name} as text. *)
val concept_name_of_ref : Names.GlobRef.t -> string

(** {!concept_name_of_ref} as a [Pp.t]. *)
val pp_concept_name_of_ref : Names.GlobRef.t -> Pp.t

(** Pretty-print just the (unqualified) name of a global. *)
val pp_global_name : Common.kind -> Names.GlobRef.t -> Pp.t

(** {2 Full paths and module names} *)

(** Pretty-print a module path. *)
val pp_modname : Names.ModPath.t -> Pp.t

(** The name of the struct the module [mp] is written as, at its
    declaration: {!pp_modname}, escaped where it is reserved. *)
val module_struct_name : Names.ModPath.t -> Pp.t

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

(** Whether the inductive is a record. *)
val is_record_inductive : Names.GlobRef.t -> bool

(** Whether the inductive is local. *)
val is_local_inductive : Names.GlobRef.t -> bool

(** [Tglob (r, args, es)], the inductive [r] applied, as a type: a local
    inductive is in scope under its own name, any other is written in its own
    scope ([Tnamespace]), which the printer places where its struct was put. *)
val inductive_type : Names.GlobRef.t -> Minicpp.cpp_type list -> Minicpp.cpp_expr list -> Minicpp.cpp_type

(** The name with its final component capitalized. *)
val capitalize_base : Cpp_name.t -> Cpp_name.t

(** [String.capitalize_ascii] of the name's text: the first character of its
    outermost qualifier, or of its base when it has none. *)
val capitalize_initial : Cpp_name.t -> Cpp_name.t

(** An inductive's name, and whether it is a non-local inductive's, which
    is capitalized and stands for the inductive's namespace wrapper. *)
val inductive_name : Names.GlobRef.t -> Cpp_name.t * bool

(** Whether an enum name collides with its parent's name. *)
val enum_name_collides_with_parent : Names.GlobRef.t -> bool

(** Capitalize an enum's (unqualified) declared name for the given global. *)
val capitalize_enum_name : string -> Names.GlobRef.t -> string

(** An enum's name, its final component capitalized unless that collides
    with its parent module's struct name. *)
val enum_name : Cpp_name.t -> Names.GlobRef.t -> Cpp_name.t

(** The name of a promoted inductive, which is its module's struct, from its
    resolved name. *)
val promoted_name : Cpp_name.t -> Cpp_name.t

(** The name without a trailing [A::A] qualifier repeating its final
    component; [allow_bare] also collapses an unqualified-but-for-it [A::A]
    to [A]. *)
val dedup_tail : ?allow_bare:bool -> Cpp_name.t -> Cpp_name.t

(** The C++ type name of an inductive. *)
val inductive_type_name : Names.GlobRef.t -> Cpp_name.t

(** {!inductive_type_name} as a document. *)
val pp_inductive_type_name : Names.GlobRef.t -> Pp.t

(** How an inductive's struct is spelled where it is declared. *)
type struct_spelling =
  | Eponymous_record_name  (** Its module's struct's name, capitalised. *)
  | Capitalized  (** Its own name, capitalised. *)
  | As_declared  (** Its own name. *)

(** The spelling of an inductive's struct at its declaration, [local] where
    the declaration is rendered among the inductives local to it; [merged]
    says whether its namespace wrapper is merged with it, as a reference
    sees it ({!is_merged_inductive} by default), and [promoted]
    whether it is promoted where it is declared. *)
val struct_spelling :
  ?merged:(Names.GlobRef.t -> bool) ->
  ?promoted:(Names.GlobRef.t -> bool) ->
  local:bool ->
  Names.GlobRef.t ->
  struct_spelling

(** An enum's name where it is declared ({!pp_inductive_type_name} there). *)
val enum_declaration_name : Names.GlobRef.t -> string

(** {!struct_spelling} as a string. *)
val struct_declaration_name :
  ?merged:(Names.GlobRef.t -> bool) ->
  ?promoted:(Names.GlobRef.t -> bool) ->
  local:bool ->
  Names.GlobRef.t ->
  string

(** The [typename] prefix required for the given name, if qualified. *)
val typename_prefix_for : Cpp_name.t -> Pp.t

(** {2 Struct and namespace qualification} *)

(** The struct qualifiers needed in front of a global's type name, written
    otherwise as given, from the given context. *)
val struct_scopes_for : Names.GlobRef.t -> Cpp_name.t -> Cpp_name.scope list

(** The global-scope qualifier needed in front of an inductive's type name,
    written otherwise as given, where a nested struct shadows it. *)
val global_scopes_for : Names.GlobRef.t -> Cpp_name.t -> Cpp_name.scope list

(** {!Cpp_state.wrapper_qualify}. *)
val wrapper_qualify : Names.GlobRef.t -> Cpp_name.t -> Cpp_name.t

(** The name a type is written under from outside the wrapper struct that owns
    it; the name unchanged while that struct's own body is being printed. *)
val wrapper_qualified_type_name : Names.GlobRef.t -> Cpp_name.t -> Cpp_name.t

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

(** Cached: the C++ inductive kind of the global, if any. *)
val get_ind_kind_cached : Names.GlobRef.t -> Minicpp.cpp_ind_kind option

(** Cached: whether the global is an enum. *)
val is_enum_cached : Names.GlobRef.t -> bool

(** Cached: whether the global is a record. *)
val is_record_cached : Names.GlobRef.t -> bool

(** {2 Method receivers} *)

(** The position of the [this] argument for a method global, if any. *)
val lookup_method_this_pos : Names.GlobRef.t -> int option

(** [method_type_args n tys] -- of the type arguments [tys] a reference to
    the method [n] was instantiated at, the ones a call must write: the
    receiver's struct carries its own parameters, and the parameters the
    method's plan drops are not in its signature at all. *)
val method_type_args : Names.GlobRef.t -> Minicpp.cpp_type list -> Minicpp.cpp_type list

(** Sets of identifiers ([Names.variable]). *)
module IdSet : Set.S with type elt = Names.variable
