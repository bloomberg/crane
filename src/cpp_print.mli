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

(** [write_decl env decl] is a settled declaration a file writes, with what
    placing the declarations it needs reads ({!Cpp_ast.Needs}). *)
val write_decl : Common.env -> Cpp_erasure.settled -> Cpp_ast.t

(** [absorbs ~homed d]: whether [d] writes a wrapper struct holding a
    wrapper module's declarations, which are members of it: one [homed]
    names, with the module, as planned. *)
val absorbs : homed:(string * ModPath.t) list -> Cpp_erasure.settled -> bool

(** [write_absorbing ctx ~homed env d] is [d], which {!absorbs}, as
    {!write_decl} writes it at the position [ctx], each wrapper struct
    holding a wrapper module's declarations a {!Cpp_ast.Wrapper_struct}. *)
val write_absorbing :
  Cpp_state.render_ctx -> homed:(string * ModPath.t) list -> Common.env -> Cpp_erasure.settled -> Cpp_ast.t

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

(** What placing the declarations [decl], written in the module [module_] in
    the file [file], needs reads ({!Cpp_ast.Needs}), as planned. *)
val planned_needs : file:Common.file -> module_:Names.ModPath.t -> Cpp_erasure.settled -> Cpp_ast.Needs.t

(** [unprinted ctx ~module_ env decl] is [decl], written at the position
    [ctx] in the module [module_], to be printed where the tree puts it
    ({!Cpp_ast.print}), with what placing the declarations it needs reads,
    as planned. *)
val unprinted : Cpp_state.render_ctx -> module_:Names.ModPath.t -> Common.env -> Cpp_erasure.settled -> Cpp_ast.t

(** [unprinted_fields ctx ~module_ ~vl r fields] is the fields [fields] of
    the eponymous record [r], each by its name and type, their type
    variables named [vl], written at the position [ctx] in the module
    [module_], to be printed where the
    tree puts them, with what placing the declarations they need reads: the
    synthesised templates they write, as planned, and the constrained
    structs they name.  Under [CRANE_CHECK_IR] the templates are spelled
    again and compared. *)
val unprinted_fields :
  Cpp_state.render_ctx ->
  module_:ModPath.t -> vl:Id.t list -> GlobRef.t -> (string * cpp_type) list -> Cpp_ast.t

(** [global_names frames globals] asks for [globals] by name at each of
    [frames]: each whose name is decided -- printing decides none -- as a
    type, as a term and as a type class's concept, an inductive as a value
    too. *)
val global_names :
  Cpp_resolution.frame list -> GlobRef.t list -> (Cpp_resolution.frame * Cpp_resolution.key) list

(** What printing a declaration not yet printed names through the type and
    expression printers, at the frames inside it it names them at, for
    {!Cpp_ast.resolve} to resolve before it is printed: of a declaration of
    the program, every global it holds, at every frame its printing
    enters. *)
val unprinted_names : Cpp_ast.declaration -> (Cpp_resolution.frame * Cpp_resolution.key) list

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
    assertion by [assertion].  Under [CRANE_CHECK_IR] it must need, printed
    there, what was planned for it where it was made. *)
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

(** [read_cpp_decl env decl] renders [decl]: for a declaration whose text is
    read, not written. *)
val read_cpp_decl : Common.env -> Cpp_erasure.settled -> Pp.t


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

(** [pp_cpp_type par vl t] renders a type where the printer is, for a type
    written outside every declaration of the tree; [par] asks for
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


(** [render_type_template ~hole text] fills hole [i] with [hole i], writing an
    unfillable hole back out as a placeholder. *)
val render_type_template : hole:(int -> Pp.t option) -> string -> Pp.t

(** {2 Wrapper structs} *)

(** The name the struct wrapping an inductive at namespace scope is written
    under. *)
val nspace_wrapper_name : GlobRef.t -> string

(** Whether the inductive is written inside a wrapper other declarations were
    queued against, and so is spelled [List::list] rather than [List]. *)
val nested_in_wrapper : GlobRef.t -> bool

(** The names of the wrapper structs a declaration writes around something
    other than a sole struct merged into them, in the order it writes them:
    the structs another wrapper's declarations can be written into. *)
val unmerged_wrappers_written : Cpp_erasure.settled -> string list

(** The assertions a declaration holds back, in the order it writes them:
    those that a class's concept holds of an instance where the concept is
    declared after the struct being written, and so is the assertion. *)
val held_back_assertions : Cpp_state.render_ctx -> Cpp_erasure.settled -> Cpp_ast.assertion list

(** {2 Forward declarations} *)

(** A forward declaration of a struct or scoped enum defined at namespace
    scope: what it declares, the declaration as the tree writes it, and
    whether it is a constrained template -- one whose [requires] clause or
    concept-kinded parameter names a concept, which the header's prologue
    need not have declared. *)
type forward_declaration = {
  fwd_ref : GlobRef.t;  (** The struct or enum it declares. *)
  fwd_tree : Cpp_ast.t;
  fwd_constrained : bool;
}

(** [forward_declarations ~module_ env d] is the forward declaration of each
    struct and scoped enum [d], an element of the module [module_], defines
    at namespace scope, in the order it defines them, written as an element
    of [module_] and printed as the definition prints its head. *)
val forward_declarations : module_:ModPath.t -> Common.env -> Cpp_erasure.settled -> forward_declaration list

(** {2 Synthesised aliases} *)

(** A template synthesised to stand where a type constructor is written as a
    template template argument but has no template name of its own: an alias
    template, or a holder -- a struct over the enclosing declaration's
    parameters the body names, with the alias as its member [c]. *)
type ctor_alias = private {
  ca_base : string;  (** What its name is made from. *)
  ca_holder : bool;
  ca_declared : Cpp_ast.declared_in;  (** Where it is declared. *)
  ca_body : string;
      (** The type it abbreviates, as written where it is declared. *)
  ca_type : cpp_type;  (** That type. *)
  ca_vars : Id.t list;  (** The names of the variables it names by index. *)
}

(** The synthesised templates something a file writes writes, in the order
    written, read in the scope being written. *)
type ctor_aliases_read

(** What the finished declaration written in [file], at the position given
    there, writes; the render of the declaration there reads it back from
    the plan. *)
val ctor_aliases_written : file:Common.file -> Cpp_state.render_ctx -> Cpp_erasure.settled -> ctor_aliases_read

(** What the fields of the record [r], of types [types], write in [file],
    their type variables read as [vl]; the render of the fields there reads
    it back from the plan ({!fields_needs}). *)
val ctor_aliases_of_fields :
  file:Common.file -> Cpp_state.render_ctx -> vl:Id.t list -> GlobRef.t -> cpp_type list -> ctor_aliases_read

(** [plan_ctor_aliases written] plans the templates each file writes,
    [written file] being what is read off what [file] writes, in the order
    written: the header's, then the implementation's. *)
val plan_ctor_aliases : (Common.file -> ctor_aliases_read list) -> unit

(** The name of a template, a function of its body. *)
val ctor_alias_name : ctor_alias -> string

(** The declaration of a template, written where the tree puts it as
    declared where it is ({!Cpp_ast.Template_in}). *)
val ctor_alias_declaration : ctor_alias -> Cpp_ast.t

(** The position a template declared where the second argument says is
    written at, in the file the first is written in ({!Cpp_ast.Template_in}). *)
val ctor_alias_render_ctx : Cpp_state.render_ctx -> Cpp_ast.declared_in -> Cpp_state.render_ctx

(** The templates the file [file] declares, each once, in the order
    planned: the aliases it writes, and, in the header, every holder the
    unit writes. *)
val ctor_aliases_declared_in : file:Common.file -> ctor_alias list

(** Under [CRANE_CHECK_IR], start recording the templates the file about
    to be written spells. *)
val start_ctor_alias_census : unit -> unit

(** Under [CRANE_CHECK_IR], check what the file [file] spelled against the
    plan. *)
val check_ctor_alias_plan : file:Common.file -> unit

(** The structs the file being written has constrained forward declarations
    of; a written declaration needs those it names or defines
    ({!write_decl}). *)
val constrained_structs : GlobRef.t list ref

(** The type names the file being written introduces at file scope, as
    planned: a definition written out of line leaves them unqualified. *)
val file_scope_type_names : CString.Set.t ref

(** The type names a declaration written at namespace scope introduces
    there, as they are written. *)
val file_scope_types : Cpp_erasure.settled -> string list

(** Under [CRANE_CHECK_IR], start recording the type names the file about
    to be written introduces at file scope. *)
val start_file_scope_census : unit -> unit

(** Under [CRANE_CHECK_IR], check those against {!file_scope_type_names}. *)
val check_file_scope_types : file:Common.file -> unit

(** Whether an expression is a lambda that captures nothing, or one such
    invoked at once with no argument: the same value wherever it is evaluated
    (see {!Cpp_constants}). *)
val closed_lambda : Minicpp.cpp_expr -> bool
