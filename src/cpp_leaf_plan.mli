(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What a leaf of the tree asks of resolution and of scheduling, decided
    before it is printed: the names it is resolved for ({!unprinted_names}),
    the declarations it needs placed ahead of it ({!Cpp_ast.Needs}), and the
    synthesised templates it writes, with how it writes each type
    constructor a template template argument writes.  {!Cpp_print} prints a
    leaf from what was decided here. *)

open Names
open Minicpp

(** [read_decl ctx env decl] is a settled declaration printed at the
    position [ctx], its names resolved there first, its type constructors
    written as planned, or, before anything is planned, as decided. *)
val read_decl : Cpp_state.render_ctx -> Common.env -> Cpp_erasure.settled -> Pp.t

(** [write_decl ctx env decl] is {!read_decl}, with what placing the
    declarations it needs reads ({!Cpp_ast.Needs}). *)
val write_decl : Cpp_state.render_ctx -> Common.env -> Cpp_erasure.settled -> Cpp_ast.t

(** The position a synthesised template declared where the second argument
    says is written at, in the file the first is written in
    ({!Cpp_ast.Template_in}). *)
val ctor_alias_render_ctx : Cpp_state.render_ctx -> Cpp_ast.declared_in -> Cpp_state.render_ctx

(** [write_absorbing ctx ~homed env d] is [d], which {!Cpp_print.absorbs}, as
    {!write_decl} writes it at the position [ctx], each wrapper struct
    holding a wrapper module's declarations a {!Cpp_ast.Wrapper_struct}. *)
val write_absorbing :
  Cpp_state.render_ctx -> homed:(string * ModPath.t) list -> Common.env -> Cpp_erasure.settled -> Cpp_ast.t

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
val ctor_aliases_written : Cpp_state.render_ctx -> Cpp_erasure.settled -> Cpp_print.ctor_aliases_read

(** What the fields of the record [r], of types [types], written at the
    position given, write, their type variables read as [vl]; the render of
    the fields there reads it back from the plan. *)
val ctor_aliases_of_fields :
  Cpp_state.render_ctx -> vl:Id.t list -> GlobRef.t -> cpp_type list -> Cpp_print.ctor_aliases_read

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
