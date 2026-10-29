(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** This module turns Coq [GlobRef.t]s and inductive references into their C++
   names and qualified paths. It provides string and [Pp.t] renderings of
   globals, field names, and inductive/enum type names, together with the
   namespace and struct qualification needed to reference them from a given
   context. Cached predicates over the name-resolution cache ([with_cache],
   [*_cached]) keep repeated lookups cheap. *)

(** {2 Names of globals} *)

(** The name of a global at the position: the replacement text of an inline
    custom mapping, otherwise as resolution settles it there. *)
val global_name : Cpp_state.render_ctx -> Common.kind -> Names.GlobRef.t -> Cpp_name.t

(** The name a global is declared under, wherever it is declared: the
    replacement text of an inline custom mapping, otherwise its own short
    name. *)
val declared_name : Common.kind -> Names.GlobRef.t -> string

(** {!global_name} as text. *)
val str_global : Cpp_state.render_ctx -> Common.kind -> Names.GlobRef.t -> string

(** {!global_name} as a document. *)
val pp_global : Cpp_state.render_ctx -> Common.kind -> Names.GlobRef.t -> Pp.t

(** The name a typeclass concept is declared and referenced under at the
    position: its short name, since a concept may only appear at namespace
    scope and so carries no struct qualifier; a use in another file names
    that file's namespace. *)
val concept_name : Cpp_state.render_ctx -> Names.GlobRef.t -> Cpp_name.t

(** {!concept_name} as text. *)
val concept_name_of_ref : Cpp_state.render_ctx -> Names.GlobRef.t -> string

(** {!concept_name_of_ref} as a [Pp.t]. *)
val pp_concept_name_of_ref : Cpp_state.render_ctx -> Names.GlobRef.t -> Pp.t

(** {2 Module names} *)

(** The name of the struct the module resolution names [name] is written
    as: escaped where it is reserved. *)
val module_struct_name_of : Cpp_name.t -> Pp.t

(** The name the struct the module [mp] is written as, or the alias
    standing for it, is declared under: the module's, escaped where it is
    reserved ({!Cpp_resolution.Module_declared}). *)
val module_declared_name : Names.ModPath.t -> string

(** {2 Inductive references} *)

(** Whether the inductive is promoted at the position: promoted by the
    unit's plan, and not demoted by a frame around the body of the module
    whose element is being written. *)
val promoted_at : Cpp_state.render_ctx -> Names.GlobRef.t -> bool

(** Whether the inductive's namespace wrapper is merged with it at the
    position: it is promoted there, or no declaration was queued against
    its wrapper. *)
val merged_at : Cpp_state.render_ctx -> Names.GlobRef.t -> bool

(** {2 Name predicates and inductive/enum naming} *)

(** Whether the inductive is a record. *)
val is_record_inductive : Names.GlobRef.t -> bool

(** Whether the inductive is spelled bare at the position: the body of the
    module whose element is being written spells it bare, as planned. *)
val local_at : Cpp_state.render_ctx -> Names.GlobRef.t -> bool

(** [Tglob (r, args, es)], the inductive [r] applied, as a type: an
    inductive local where the declaration generator is is in scope under its
    own name, any other is written in its own
    scope ([Tnamespace]), which the printer places where its struct was put. *)
val inductive_type : Names.GlobRef.t -> Minicpp.cpp_type list -> Minicpp.cpp_expr list -> Minicpp.cpp_type

(** The name with its final component capitalized. *)
val capitalize_base : Cpp_name.t -> Cpp_name.t

(** [String.capitalize_ascii] of the name's text: the first character of its
    outermost qualifier, or of its base when it has none. *)
val capitalize_initial : Cpp_name.t -> Cpp_name.t

(** An inductive's name, and whether it is a non-local inductive's, which
    is capitalized and stands for the inductive's namespace wrapper. *)
val inductive_name : Cpp_state.render_ctx -> Names.GlobRef.t -> Cpp_name.t * bool

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
val inductive_type_name : Cpp_state.render_ctx -> Names.GlobRef.t -> Cpp_name.t

(** How an inductive's struct is spelled where it is declared. *)
type struct_spelling =
  | Eponymous_record_name  (** Its module's struct's name, capitalised. *)
  | Capitalized  (** Its own name, capitalised. *)
  | As_declared  (** Its own name. *)

(** The spelling of an inductive's struct at its declaration, [local] where
    the declaration is rendered among the inductives local to it; [merged]
    says whether its namespace wrapper is merged with it, as a reference
    sees it ({!merged_at}), and [promoted] whether it is promoted where it
    is declared. *)
val struct_spelling :
  merged:(Names.GlobRef.t -> bool) ->
  promoted:(Names.GlobRef.t -> bool) ->
  local:bool ->
  Names.GlobRef.t ->
  struct_spelling

(** An enum's name where it is declared ({!inductive_type_name} there). *)
val enum_declaration_name : Names.GlobRef.t -> string

(** {!struct_spelling} as a string. *)
val struct_declaration_name :
  merged:(Names.GlobRef.t -> bool) ->
  promoted:(Names.GlobRef.t -> bool) ->
  local:bool ->
  Names.GlobRef.t ->
  string

(** The [typename] prefix the name needs at the position [ctx]: where it
    is qualified inside a class template. *)
val typename_prefix_for : Cpp_state.render_ctx -> Cpp_name.t -> Pp.t

(** {2 Struct and namespace qualification} *)

(** The struct qualifiers needed in front of a global's type name, written
    otherwise as given, at the position the render context says: outside a
    struct's body, in the out-of-line definition of one of its members. *)
val struct_scopes_for : Cpp_state.render_ctx -> Names.GlobRef.t -> Cpp_name.t -> Cpp_name.scope list

(** The global-scope qualifier needed in front of an inductive's type name,
    written otherwise as given, where a nested struct shadows it. *)
val global_scopes_for : Names.GlobRef.t -> Cpp_name.t -> Cpp_name.scope list

(** {!Cpp_state.wrapper_qualify}. *)
val wrapper_qualify : Names.GlobRef.t -> Cpp_name.t -> Cpp_name.t

(** The name a type is written under from outside the wrapper struct that owns
    it; the name unchanged while that struct's own body is being printed, as
    the render context says. *)
val wrapper_qualified_type_name : Cpp_state.render_ctx -> Names.GlobRef.t -> Cpp_name.t -> Cpp_name.t

(** Whether the global must be referenced with a global-scope qualifier at
    the position [ctx]: from the out-of-line definition of a member of a
    struct that does not enclose it. *)
val needs_global_qualifier : Cpp_state.render_ctx -> Names.GlobRef.t -> bool

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

(** {2 What a declaration not yet printed names} *)

(** The module whose element is being written at the position: what the
    plan reads off something written there is keyed by it. *)
val module_written : Cpp_state.render_ctx -> Names.ModPath.t

(** The functor whose body declares module types at [mp], by its label, with
    its parameters, as {!Cpp_state.functor_concept_scopes} records it. *)
val functor_concept_scope : Names.ModPath.t -> (Names.Label.t * Names.ModPath.t list) option

(** The arguments, after the constrained module, of the concept of the module
    type [kn]: the parameters of the functor declaring it, if one does. *)
val concept_extra_args : Names.ModPath.t -> Names.ModPath.t list

(** The C++ identifier of the concept the module type at [mp] becomes, at
    its declaration and at every reference: named after the functor whose
    body declares it, where one does ({!functor_concept_scope}); qualified
    with its module where another concept shares its name
    ({!Module_plan.modtype_concept_name}); and otherwise its label
    ({!Structure_analysis.concept_name_of_label}).  Every site naming a
    module-type concept goes through this, so no two can disagree. *)
val modtype_concept_name : Names.ModPath.t -> string

(** The concept of the module type [kn], as a reference names it at the
    position.  In separate extraction a concept lives in its file's
    namespace, so a reference from another file is qualified. *)
val modtype_concept_ref : Cpp_state.render_ctx -> Names.ModPath.t -> Cpp_name.t

(** The name the struct of [id] is defined under. *)
val struct_definition_name : Cpp_state.render_ctx -> Names.GlobRef.t -> Cpp_name.t

(** The name the scoped enum of [r] is defined under. *)
val enum_definition_name : Cpp_state.render_ctx -> Names.GlobRef.t -> Cpp_name.t

(** The name the inductive type [x] is written under as a value: the struct
    a constructor's value is built through, at the position. *)
val inductive_value : Cpp_state.render_ctx -> Names.GlobRef.t -> Cpp_name.t

(** [checked key ~live n] is [n], the name the resolution pass gave [key];
    under [CRANE_CHECK_IR], [live ()], the name resolution gives it where it
    is printed, must be the same. *)
val checked : Cpp_resolution.key -> live:(unit -> Cpp_name.t) -> Cpp_name.t -> Cpp_name.t

(** An anomaly: [key] was printed before it was resolved. *)
val unresolved : Cpp_resolution.key -> 'a

(** [name_from names frame key ~live] is the name [names] gives [key] at
    [frame], {!checked}.  A table not yet resolved, or one that was but not
    for this, is an anomaly. *)
val name_from :
  Cpp_resolution.table -> Cpp_resolution.frame -> Cpp_resolution.key -> live:(unit -> Cpp_name.t) -> Cpp_name.t

(** [next entered c] is the position [c] is after entering the scope
    [entered] inside it: a function of the two. *)
val next : Cpp_resolution.entered -> Cpp_state.render_ctx -> Cpp_state.render_ctx

(** [enter_from c entered k] is [k] of the position after entering the
    scope [entered] from [c] ({!next}), what is visible there included.  It
    installs nothing ({!Cpp_state.entering_scope}): [k] is handed it. *)
val enter_from : Cpp_state.render_ctx -> Cpp_resolution.entered -> (Cpp_state.render_ctx -> 'a) -> 'a

(** [entering_from c l k] is [k] of the position after entering each scope
    of [l] from [c], in order ({!enter_from}). *)
val entering_from : Cpp_state.render_ctx -> Cpp_resolution.entered list -> (Cpp_state.render_ctx -> 'a) -> 'a

(** [at_frame c frame k] is [k] of the position after entering each scope
    of [frame] from [c], outermost first ({!enter_from}): how resolving what
    a declaration names at a frame enters it. *)
val at_frame : Cpp_state.render_ctx -> Cpp_resolution.frame -> (Cpp_state.render_ctx -> 'a) -> 'a

(** [key] named at the position [c], from what is visible there
    ({!Cpp_state.render_ctx.rc_visibility}), whatever declaration is being
    written: what {!Cpp_resolution.resolve} is given, at each frame, and
    what a printed name is checked against.  A position nothing planned the
    visibility of is an anomaly. *)
val live_name : Cpp_state.render_ctx -> Cpp_resolution.key -> Cpp_name.t
