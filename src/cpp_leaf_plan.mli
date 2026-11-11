(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What a leaf of the C++ tree ({!Cpp_ast}) asks of resolution and of
    scheduling, decided before it is printed and after the unit's
    declarations are finished: the names it is resolved for ({!unprinted_names}),
    the declarations it needs placed ahead of it ({!Cpp_ast.Needs}), and the
    synthesised templates it writes, with how it writes each type
    constructor a template template argument writes.  {!Cpp_print} prints a
    leaf from what was decided here. *)

open Names
open Minicpp

(** What a file writes that places the templates it writes: a declaration,
    or the fields of the eponymous record merged into a module's struct,
    which no declaration holds. *)
type written = Written_declaration of cpp_decl | Written_fields of GlobRef.t

(** The synthesised templates something a file writes writes, in the order
    written, read in the scope being written: what it is, in the module it
    is written in, the templates, and how it writes each type constructor
    it writes as a template template argument. *)
type ctor_aliases_read = {
  read_written : ModPath.t * written;
  read_aliases : Cpp_print.ctor_alias list;
  read_uses : Cpp_state.tyctor_use list;
}

(** [read_decl ctx env decl] is a settled declaration printed at the
    position [ctx], its names resolved there first, its type constructors
    written as planned, or, before anything is planned, as decided. *)
val read_decl : Cpp_state.render_ctx -> Common.env -> Cpp_erasure.settled -> Pp.t

(** The types the declaration, written at namespace scope, introduces
    there, by the entity each declares: its own, through a template head and
    an anonymous namespace, and a struct's -- but not those of what a wrapper
    struct holds, which are its members. *)
val file_scope_types : Cpp_erasure.settled -> Names.GlobRef.t list

(** The head of every global type in a type. *)
val type_heads : cpp_type -> GlobRef.t list

(** The globals a declaration's printing writes beside those it holds: a
    template template argument's head, the primitive integer type, the
    custom a custom match or a block custom is written from. *)
val globals_written_beside : cpp_decl -> GlobRef.t list

(** Whether [d] is an assertion the struct being written holds back until
    after it, writing nothing for it here. *)
val is_held_back_assertion : Cpp_state.render_ctx -> Cpp_erasure.settled -> bool

(** Whether a function declaration writes a qualifier into a struct or a
    template parameter, in its name, result or parameters, asked of the
    declaration rather than of its rendering: each name is the one
    {!Cpp_print.pp_cpp_type} writes, from the same heads, at the position
    given, of the names [names] as {!Cpp_print.print_unprinted} reads them.
    [None] for anything but a function declaration, and where only the
    rendering can tell -- an expression's type, a type constructor named as
    a template argument. *)
val resolved_names_into_a_struct : Cpp_state.render_ctx -> Cpp_resolution.table -> Cpp_erasure.settled -> bool option

(** Whether one thing a rendering writes ({!Cpp_name.written}) is a
    qualifier naming into a struct or a template parameter rather than a
    namespace: a tagged scope by its kind, untagged text by the identifier in
    front of each [::], which passes only as an included library's
    namespace. *)
val writes_into_a_struct : Cpp_name.written -> bool

(** Whether a declaration, written as a member of a struct body, is a static
    function declaration ending at its semicolon. *)
val is_static_member_declaration : cpp_decl -> bool

(** [stand_ins t] is, for each type the declarations of [t] declare, a
    member alias of it ({!Cpp_ast.global_alias}): what a struct holds in
    place of [t] once [t] is moved out of it to namespace scope.  Only an
    alias's name and an enum's are spelled the way a reference to them is,
    so only those are stood in for. *)
val stand_ins : Cpp_ast.t -> Cpp_ast.t list

(** The wrapper structs the declaration writes around something other than
    a sole struct merged into them, in the order it writes them, each by the
    wrapper and its name spelled to be compared with a wrapper module's
    ({!Cpp_names.wrapper_spelling}). *)
val unmerged_wrappers_written : Cpp_erasure.settled -> (Names.GlobRef.t * string) list

(** Whether the declaration writes a wrapper struct holding a wrapper
    module's declarations: that of a wrapper the list gives a module. *)
val absorbs : homed:(Names.GlobRef.t * Names.ModPath.t) list -> Cpp_erasure.settled -> bool

(** [write_decl ctx env decl] is {!read_decl}, with what placing the
    declarations it needs reads ({!Cpp_ast.Needs}). *)
val write_decl : Cpp_state.render_ctx -> Common.env -> Cpp_erasure.settled -> Cpp_ast.t

(** The position a synthesised template declared where the second argument
    says is written at, in the file the first is written in
    ({!Cpp_ast.Template_in}). *)
val ctor_alias_render_ctx : Cpp_state.render_ctx -> Cpp_ast.declared_in -> Cpp_state.render_ctx

(** [write_absorbing ctx ~homed env d] is [d], which {!absorbs}, as
    {!write_decl} writes it at the position [ctx], each wrapper struct
    holding a wrapper module's declarations a {!Cpp_ast.Wrapper_struct}. *)
val write_absorbing :
  Cpp_state.render_ctx -> homed:(Names.GlobRef.t * ModPath.t) list -> Common.env -> Cpp_erasure.settled -> Cpp_ast.t

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
    too; and each custom's text. *)
val global_names :
  Cpp_resolution.frame list -> GlobRef.t list -> (Cpp_resolution.frame * Cpp_resolution.key) list

(** The globals writing the type names, for {!global_names}: those whose
    names it writes and the customs it is written from. *)
val type_globals : Minicpp.cpp_type -> GlobRef.t list

(** The globals printing the declaration [d] names, for {!global_names}:
    those it holds, those written beside them -- a template template
    argument's head, the primitive integer type, the custom a custom match
    or a block custom is written from -- and those it declares. *)
val declaration_globals : Cpp_erasure.settled -> GlobRef.t list

(** What printing a declaration not yet printed names through the type and
    expression printers, at the frames inside it it names them at, for
    {!Cpp_ast.resolve} to resolve before it is printed: of a declaration of
    the program, every global it holds, at every frame its printing
    enters. *)
val unprinted_names : Cpp_ast.declaration -> (Cpp_resolution.frame * Cpp_resolution.key) list

(** What the finished declaration written at the position given, in the
    file it is in, writes; the render of the declaration there reads it back
    from the plan. *)
val ctor_aliases_written : Cpp_state.render_ctx -> Cpp_erasure.settled -> ctor_aliases_read

(** What the fields of the record [r], of types [types], written at the
    position given, write, their type variables read as [vl]; the render of
    the fields there reads it back from the plan. *)
val ctor_aliases_of_fields :
  Cpp_state.render_ctx -> vl:Id.t list -> GlobRef.t -> cpp_type list -> ctor_aliases_read

(** {!Cpp_print.print_unprinted}; under [CRANE_CHECK_IR] a declaration, a
    record's fields or a synthesised template must need, and write their
    type constructors, printed there, as was planned for them where they
    were made. *)
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

(** The structs and scoped enums [d] defines at namespace scope, in the
    order it defines them, and what each declares. *)
val structs_defined : Cpp_erasure.settled -> Cpp_ast.defined list

(** The struct or enum a definition declares. *)
val defined_ref : Cpp_ast.defined -> Names.GlobRef.t

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
  fwd_ref : Names.GlobRef.t;  (** The struct or enum it declares. *)
  fwd_tree : Cpp_ast.t;  (** The declaration, as an element of its module. *)
  fwd_constrained : bool;  (** Whether it is a constrained template. *)
}

(** [forward_declarations ctx ~module_ env d] is the forward declaration of
    each struct and scoped enum [d], an element of the module [module_]
    written at the position [ctx], defines at namespace scope, in the order
    it defines them, written as an element of [module_] and printed as the
    definition prints its head. *)
val forward_declarations :
  Cpp_state.render_ctx -> module_:Names.ModPath.t -> Common.env -> Cpp_erasure.settled -> forward_declaration list

(** [plan_ctor_aliases written] plans the templates each file writes,
    [written file] being what is read off what [file] writes, in the order
    written: the header's, then the implementation's. *)
val plan_ctor_aliases : (Common.file -> ctor_aliases_read list) -> unit

(** The declaration of a template, written where the tree puts it as
    declared where it is ({!Cpp_ast.Template_in}). *)
val ctor_alias_declaration : Cpp_print.ctor_alias -> Cpp_ast.t

(** The templates the file [file] declares, each once, in the order
    planned: the aliases it writes, and, in the header, every holder the
    unit writes. *)
val ctor_aliases_declared_in : file:Common.file -> Cpp_print.ctor_alias list

(** Under [CRANE_CHECK_IR], check what the file [file] spelled against the
    plan. *)
val check_ctor_alias_plan : file:Common.file -> unit

(** The structs the file being written has constrained forward declarations
    of; a written declaration needs those it names or defines
    ({!write_decl}). *)
val constrained_structs : GlobRef.t list ref
