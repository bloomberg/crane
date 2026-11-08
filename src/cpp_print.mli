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

(** The wrapper structs a declaration writes around something other than a
    sole struct merged into them, in the order it writes them, each named by
    the function given: the structs another wrapper's declarations can be
    written into. *)
val unmerged_wrappers_named : name:(GlobRef.t -> string) -> Cpp_erasure.settled -> string list

(** [d], which absorbs a wrapper module ({!Cpp_leaf_plan.absorbs}), written at the position given, each wrapper
    struct holding a wrapper module's declarations a
    {!Cpp_ast.Wrapper_struct}, each member writing its type constructors
    as [tyctors], planned for [d], says. *)
val absorbing_at :
  Cpp_state.render_ctx ->
  homed:(string * ModPath.t) list ->
  ?tyctors:Cpp_state.tyctor_use list ->
  Common.env ->
  Cpp_erasure.settled ->
  Cpp_ast.t

(** The head of every global type in a type. *)
val type_heads : cpp_type -> GlobRef.t list

(** The globals a declaration's printing writes beside those it holds: a
    template template argument's head, the primitive integer type, the
    custom a custom match or a block custom is written from. *)
val globals_written_beside : cpp_decl -> GlobRef.t list

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

(** Whether [d] is an assertion the struct being written holds back until
    after it, writing nothing for it here. *)
val is_held_back_assertion : Cpp_state.render_ctx -> Cpp_erasure.settled -> bool

(** Whether a function declaration writes a qualifier into a struct or a
    template parameter, in its name, result or parameters, asked of the
    declaration rather than of its rendering: each name is the one
    {!pp_cpp_type} writes, from the same heads, at the position given, of
    the names [names] as {!print_unprinted} reads them.  [None] for anything but
    a function declaration, and where only the rendering can tell -- an
    expression's type, a type constructor named as a template argument. *)
val resolved_names_into_a_struct : Cpp_state.render_ctx -> Cpp_resolution.table -> Cpp_erasure.settled -> bool option

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

(** [stand_ins t] is, for each type the declarations of [t] declare, a
    member alias of it ({!Cpp_ast.global_alias}): what a struct holds in
    place of [t] once [t] is moved out of it to namespace scope.  Only an
    alias's name and an enum's are spelled the way a reference to them is,
    so only those are stood in for. *)
val stand_ins : Cpp_ast.t -> Cpp_ast.t list

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

(** Whether one thing a rendering writes ({!Cpp_name.written}) is a
    qualifier naming into a struct or a template parameter rather than a
    namespace: a tagged scope by its kind, untagged text by the identifier in
    front of each [::], which passes only as an included library's
    namespace. *)
val writes_into_a_struct : Cpp_name.written -> bool

(** Whether a declaration, written as a member of a struct body, is a static
    function declaration ending at its semicolon. *)
val is_static_member_declaration : cpp_decl -> bool

(** Doc-comment lines for [name], or nothing when none is registered. *)
val pp_doc_comment_for_name : ?indent:string -> string -> Pp.t

(** The break between two declaration groups ({!Cpp_ast.cut2}). *)
val cut2 : unit -> Pp.t

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

(** {2 Synthesised aliases} *)

(** A template synthesised to stand where a type constructor is written as a
    template template argument but has no template name of its own: an alias
    template, or a holder -- a struct over the enclosing declaration's
    parameters the body names, with the alias as its member [c]. *)
type ctor_alias = Cpp_state.ctor_alias = {
  ca_base : string;  (** What its name is made from. *)
  ca_holder : bool;
  ca_declared : Cpp_ast.declared_in;  (** Where it is declared. *)
  ca_body : string;
      (** The type it abbreviates, as written where it is declared. *)
  ca_type : cpp_type;  (** That type. *)
  ca_vars : Id.t list;  (** The names of the variables it names by index. *)
  ca_uses : Cpp_state.tyctor_use list;  (** How its body writes the type constructors in it. *)
}

(** The name of a template, a function of its body. *)
val ctor_alias_name : ctor_alias -> string

(** What a synthesised template's body is decided from.  [tyctor_constructor t]
    is the constructor a type constructor position writes; [cut_at_argument_list s]
    is [s] up to its first template argument list; [identifier_tokens s] the
    identifiers [s] writes, as whole tokens; [applied_to_sentinel_alone ctx t]
    whether [t], a constructor applied to the sentinel, is written as a
    template name applied to it alone, read off its structure, if that says;
    [foreign_text fr] the text an instantiated mapping was instantiated
    from. *)
val tyctor_constructor : cpp_type -> cpp_type
val cut_at_argument_list : string -> string
val identifier_tokens : string -> string list
val applied_to_sentinel_alone : Cpp_state.render_ctx -> cpp_type -> bool option
val foreign_text : foreign -> string
val ctor_alias_tvar : string

(** Under [CRANE_CHECK_IR], start recording the templates the file about
    to be written spells. *)
val start_ctor_alias_census : unit -> unit

(** The templates the file being written spelled where nothing collected
    them since {!start_ctor_alias_census}, under [CRANE_CHECK_IR]; starts
    the census again. *)
val take_ctor_aliases_spelled : unit -> ctor_alias list

(** The type names a declaration written at namespace scope, at the
    position given, introduces there, as they are written. *)
val file_scope_types : Cpp_state.render_ctx -> Cpp_erasure.settled -> string list

(** Under [CRANE_CHECK_IR], start recording the type names the file about
    to be written introduces at file scope. *)
val start_file_scope_census : unit -> unit

(** Under [CRANE_CHECK_IR], check those against the ones planned
    ({!Cpp_state.file_scope_types_of}). *)
val check_file_scope_types : file:Common.file -> unit

