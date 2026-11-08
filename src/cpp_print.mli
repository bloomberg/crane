(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Rendering MiniCpp as C++ source text.

    The declaration printer's input is a settled declaration (see
    {!Cpp_erasure.settled}): it runs no compiler pass.  The registries below
    are the printer's remaining state: forward declarations and synthesised
    aliases it mints while rendering and the assembly drains. *)

open Names
open Minicpp

(** {2 Rendering} *)

(** {!pp_cpp_type} at the position given. *)
val pp_cpp_type_at : Cpp_state.render_ctx -> bool -> Id.t list -> cpp_type -> Pp.t

(** The name of a module a declaration of the tree names, as
    {!Cpp_ast.resolve} resolved it where the declaration is written; under
    [CRANE_CHECK_IR], checked against the name resolution gives it at the
    position it is printed at ({!Cpp_names.live_name}).  A module not yet
    resolved is an anomaly. *)
val resolved_module : Cpp_state.render_ctx -> Cpp_ast.module_ref -> Cpp_name.t

(** {!resolved_module} for the concept of a type class. *)
val resolved_class_concept : Cpp_state.render_ctx -> Cpp_ast.global_ref -> Cpp_name.t

(** {!resolved_module} for a type. *)
val resolved_type_name : Cpp_state.render_ctx -> Cpp_ast.global_ref -> Cpp_name.t

(** {!resolved_module} for the concept of a module type. *)
val resolved_concept : Cpp_state.render_ctx -> Cpp_ast.concept_ref -> Cpp_name.t

(** [name_in ctx names frame key] is the name [names] gives [key] at
    [frame], checked as {!resolved_module} is, at the position [ctx].  A
    table not yet resolved, or one that was but not for this, is an
    anomaly. *)
val name_in : Cpp_state.render_ctx -> Cpp_resolution.table -> Cpp_resolution.frame -> Cpp_resolution.key -> Cpp_name.t

(** The text of a declaration not yet printed, printed at the position its
    spelling enters, a module type's concept by [modtype_concept] and an
    assertion by [assertion], from the names resolved for it. *)
val print_unprinted :
  Cpp_state.render_ctx ->
  modtype_concept:
    (Cpp_state.render_ctx ->
    names:Cpp_resolution.table ->
    params:ModPath.t list ->
    ModPath.t ->
    Modtype_concept.t ->
    Pp.t ) ->
  assertion:(Cpp_state.render_ctx -> Cpp_ast.assertion -> Pp.t) ->
  Cpp_ast.unprinted ->
  Pp.t

(** [read_cpp_decl ctx env decl] renders [decl] at the position [ctx]: for
    a declaration whose text is read, not written. *)
val read_cpp_decl : Cpp_state.render_ctx -> Common.env -> Cpp_erasure.settled -> Pp.t


(** How a member is written: in the struct with or without its body, or out
    of line. *)
type member_mode

(** [pp_cpp_field ctx env f] renders a struct member at the position
    [ctx].  [struct_name] is the enclosing struct's name, for constructors
    and destructors. *)
val pp_cpp_field :
  ?struct_name:Pp.t -> ?mode:member_mode -> Cpp_state.render_ctx -> Common.env -> cpp_field -> Pp.t

(** [pp_type ctx t] renders the type [t], naming no variable by index, at
    the position [ctx]. *)
val pp_type : Cpp_state.render_ctx -> cpp_type -> Pp.t

(** [pp_cpp_type par vl t] renders a type at the start of the header, where
    nothing may be named, for a diagnostic of a type that names nothing; [par] asks for
    parentheses where precedence needs them, [vl] names the type variables
    by index.  [~lead:false] drops the leading [typename] of a dependent name
    about to be embedded in a longer one. *)
val pp_cpp_type : ?lead:bool -> bool -> Id.t list -> cpp_type -> Pp.t

(** Doc-comment lines for [name], or nothing when none is registered. *)
val pp_doc_comment_for_name : ?indent:string -> string -> Pp.t

(** The break between two declaration groups ({!Cpp_ast.cut2}). *)
val cut2 : unit -> Pp.t

(** {2 The printer's spelling, as planning asks it}

    Planning's questions about what a declaration writes
    ({!Cpp_leaf_plan.declaration_names_into_a_struct},
    {!Cpp_leaf_plan.file_scope_types}) are asked of the same heads and names
    the printer writes, not of a rendering. *)

(** A type's name as the type printer writes it: the qualifiers in front of
    it, the name itself, whether a dependent qualifier in it asks for
    [typename], and whether template arguments following it need the
    [template] disambiguator. *)
type written_head = {
  outer : Cpp_name.scope list;
  head : Cpp_name.t;
  typename : bool;
  template_keyword : bool;
}

(** A name written with nothing in front of it. *)
val unqualified_head : Cpp_name.t -> written_head

(** The head of a global type no custom mapping inlines, at the position,
    [applied] when template arguments follow it. *)
val glob_head : Cpp_state.render_ctx -> GlobRef.t -> applied:bool -> written_head

(** The head of an inductive written through the struct it is declared in. *)
val inductive_head : Cpp_state.render_ctx -> GlobRef.t -> applied:bool -> written_head

(** The qualifiers a member of the struct being defined out of line is
    written with when named outside that struct's body, or [None] where it
    is written bare. *)
val member_scopes : Cpp_state.render_ctx -> Id.t -> Cpp_name.scope list option

(** The spelling of an external type's name. *)
val external_type_name : string -> string

(** The primitive integer type, if registered: what a literal of it is
    written through. *)
val uint63_type : unit -> GlobRef.t option

(** The type name a declaration introduces at the position, for the shapes
    whose spelling is settled by the declaration. *)
val decl_type_name : Cpp_state.render_ctx -> cpp_decl -> Pp.t option

(** The name the struct of the inductive is defined under. *)
val struct_definition_name : Cpp_state.render_ctx -> GlobRef.t -> Pp.t

(** {2 Custom type templates} *)


(** [pp_type_pieces r pieces arg] writes the type mapping [r] instantiated
    in [pieces], hole [i] filled with [arg i] -- in a module type's concept,
    each argument written as the concept qualifies it.  Every hole is
    supplied, an erased argument included ({!Modtype_concept.concept_type}). *)
val pp_type_pieces : GlobRef.t -> foreign_piece list -> (int -> Pp.t option) -> Pp.t

(** {2 Wrapper structs} *)

(** The name the struct wrapping an inductive at namespace scope is written
    under at the position. *)
val nspace_wrapper_name : Cpp_state.render_ctx -> GlobRef.t -> string

(** Under [CRANE_CHECK_IR], the type name the declaration given introduces
    at file scope where written at the position given, noted as written in
    the file. *)
val note_file_scope_type : Cpp_state.render_ctx -> cpp_decl -> unit

(** {2 Synthesised aliases} *)

(** A template synthesised to stand where a type constructor is written as a
    template template argument but has no template name of its own: an alias
    template, or a holder -- a struct over the enclosing declaration's
    parameters the body names, with the alias as its member [c]. *)
type ctor_alias = Cpp_state.ctor_alias = {
  ca_base : string;  (** What its name is made from. *)
  ca_holder : Cpp_state.holder_parameter list option;  (** A holder's parameters. *)
  ca_declared : Cpp_ast.declared_in;  (** Where it is declared. *)
  ca_body : string;
      (** The type it abbreviates, as written where it is declared. *)
  ca_type : cpp_type;  (** That type. *)
  ca_vars : Id.t list;  (** The names of the variables it names by index. *)
  ca_uses : Cpp_state.tyctor_use list;  (** How its body writes the type constructors in it. *)
}

(** The name of a template, a function of its body. *)
val ctor_alias_name : ctor_alias -> string

(** How the type constructor given, naming the variables given by index, is
    written at the position given: as the plan of the leaf being printed
    says, or as planning, deciding it there, decides and notes. *)
val tyctor_written : Cpp_state.render_ctx -> Id.t list -> cpp_type -> (ctor_alias * Cpp_state.holder_argument list) option

(** The template given, spelled at the position given: collected where the
    position collects them, and otherwise, under [CRANE_CHECK_IR], noted as
    spelled in the file. *)
val note_ctor_alias_spelled : Cpp_state.render_ctx -> ctor_alias -> unit

(** What a synthesised template's body is decided from.  [tyctor_constructor t]
    is the constructor a type constructor position writes; [cut_at_argument_list s]
    is [s] up to its first template argument list; [identifier_tokens s] the
    identifiers [s] writes, as whole tokens; [foreign_text fr] the text an
    instantiated mapping was instantiated from. *)
val tyctor_constructor : cpp_type -> cpp_type
val cut_at_argument_list : string -> string
val identifier_tokens : string -> string list
val foreign_text : foreign -> string
val ctor_alias_tvar : string

(** Under [CRANE_CHECK_IR], start recording the templates the file about
    to be written spells. *)
val start_ctor_alias_census : unit -> unit

(** The templates the file being written spelled where nothing collected
    them since {!start_ctor_alias_census}, under [CRANE_CHECK_IR]; starts
    the census again. *)
val take_ctor_aliases_spelled : unit -> ctor_alias list

(** Under [CRANE_CHECK_IR], start recording the type names the file about
    to be written introduces at file scope. *)
val start_file_scope_census : unit -> unit

(** Under [CRANE_CHECK_IR], check those against the ones planned
    ({!Cpp_state.file_scope_types_of}). *)
val check_file_scope_types : file:Common.file -> unit

