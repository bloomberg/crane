(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Which C++ declarations a MiniML declaration becomes.

   This module turns MiniML inductives ([ml_ind]) and declarations
   ([ml_decl]) into {!Minicpp.cpp_decl} values, between translation
   ({!Translation}, {!Gen_decls}) and the printer ({!Cpp}).  Everything a
   declaration becomes is generated once, ahead of both files
   ({!generate_ahead}), finished in the unit's program
   ({!Unit_program}), and taken from there by each file's pass:

   {ul
   {- the source-file family ({!impl_decls}) gives the full definitions
      that go into the generated [.cpp];}
   {- the header family ({!header_decls}) gives the declarations that go
      into the generated [.h];}
   {- the [_ahead] family ({!header_element_ahead}, {!impl_element_ahead})
      reads the same answers without taking them, for planning.}}

   It also owns what the header plans about a module's body: its scope
   ({!header_scope}), where its concepts go ({!plan_concepts}), and the
   position and name resolution of a declaration as written
   ({!spelling_position}, {!resolver_at}).

   Each answer pairs a declaration with the name environment its
   sub-expressions are printed in; {!pp_decls} prints them. *)

(** Declarations as generated, each with the name environment it is printed
    in. *)
type generated = (Common.env * Minicpp.cpp_decl) list

(** Declarations finished for the printer: what one MiniML declaration
    became, as the unit's program finished it ({!Unit_program.finish}), in
    CppIR. *)
type rendered = (Common.env * Cpp_ir.Resolved.Decl.t) list

(** Print the declarations an entry point answered with, at the position
    given. *)
val pp_decls : Cpp_state.render_ctx -> rendered -> Cpp_ast.t

(** What a type class instance becomes: the struct carrying its methods, and,
    for a ground instance, the [static_assert] checking it against the class's
    concept.  Both belong at namespace scope, wherever the instance was
    declared. *)
val instance_decls :
  Names.GlobRef.t -> Miniml.ml_ast -> Miniml.ml_type -> generated

(** The callable plan of each method of the instance's struct, by name: the
    head {!instance_decls} declares it with, planned without a body. *)
val plan_instance_methods :
  Names.GlobRef.t -> Miniml.ml_ast -> Miniml.ml_type -> (Names.Id.t * Callable_abi.t) list

(** [generated_once ~module_ ?on_reuse ?on_peek ?planned node gen] is [gen ()] ahead
    of the files ({!generating_ahead}), recorded by the physical MiniML node
    [node] and the module [module_] it is generated in -- the module whose
    element it is, as for everything below that takes one -- and handed to
    [planned] to plan what
    taking it needs.  A file's pass takes what was recorded there --
    emission decides nothing the plan has not, so it is what the pass would
    generate -- handing it to [on_reuse] to replay any effect generating it
    had; that nothing was is an anomaly.  [CRANE_CHECK_IR] regenerates and
    checks.  Read while peeking ({!header_element_ahead}), it is what was
    recorded, handed to [on_peek] in place of [on_reuse]. *)
val generated_once :
  module_:Names.ModPath.t ->
  ?on_reuse:(Gen_decls.generated_fun list -> unit) ->
  ?on_peek:(Gen_decls.generated_fun list -> unit) ->
  ?planned:(Gen_decls.generated_fun list -> unit) ->
  'node ->
  (unit -> Gen_decls.generated_fun list) ->
  Gen_decls.generated_fun list

(** [generating_ahead f] runs [f], a walk generating every function before
    either file is rendered, recording what {!generated_once} generates in
    it for both files. *)
val generating_ahead : (unit -> 'a) -> 'a

(** Begin a render of the file [file]: under [CRANE_CHECK_IR] the header
    claims the helpers it places afresh, to check them against the planned
    claims. *)
val start_render : file:Common.file -> unit

(** [source r] is the source entity [r], as an owner. *)
val source : Names.GlobRef.t -> Unit_program.owner

(** [helper_id d] is the id of the lifted helper [d] in the unit's program
    ({!Unit_program.id}): the only declaration of its own generation.
    That [d] is not a lifted helper is an anomaly. *)
val helper_id : Minicpp.cpp_decl -> Unit_program.id

(** [helpers_placed ds] is each lifted helper of [ds] under its
    {!helper_id}. *)
val helpers_placed : Minicpp.cpp_decl list -> (Unit_program.id * Minicpp.cpp_decl) list

(** [instance_ids r ds] is the id of each of [ds], the declarations of the
    instance [r]. *)
val instance_ids : Names.GlobRef.t -> generated -> Unit_program.id list

(** [instance_jobs r ds] is [ds], the declarations of the instance [r], to
    finish, each under its id. *)
val instance_jobs : Names.GlobRef.t -> generated -> Unit_program.job list

(** [instance_placed r ds helpers] is [helpers], the helpers lifted out of
    the methods of the instance [r], then [ds], its declarations, each under
    its id: how a wrapper module places an instance, as it places a lifted
    helper. *)
val instance_placed :
  Names.GlobRef.t -> generated -> Minicpp.cpp_decl list -> (Unit_program.id * Minicpp.cpp_decl) list

(** [concept_id r] is the id of the concept of the class [r]. *)
val concept_id : Names.GlobRef.t -> Unit_program.id

(** [record_methods_id r] is the id of the methods of the eponymous record
    [r] ({!Unit_program.Methods}). *)
val record_methods_id : Names.GlobRef.t -> Unit_program.id


(** What generating a declaration ahead of the files leaves for later: the
    functions it generated, which Loopify reads while finishing any function
    of the unit, so that all are registered before any is finished; what of
    it to finish; and the helpers lifted out of it, finished once everything
    else is. *)
type ahead = {
  entities : Unit_program.entity list;
      (** What was generated, as the entities a file records taking it. *)
  functions : Minicpp.cpp_decl list;
      (** The function definitions generated, registered with Loopify
          before any function of the unit is finished. *)
  finishing : Unit_program.job list;
      (** What of the declaration to finish, each under its id. *)
  helpers : Minicpp.cpp_decl list;
      (** The helpers lifted out of it, finished after everything else, each
          under its {!helper_id}. *)
  handed_on : Unit_program.job list;
      (** Declarations of its own handed on to be finished with its helpers,
          after them. *)
}

(** Nothing generated ahead. *)
val nothing_ahead : ahead

(** [functions_ahead elements]: the functions generated ahead
    ({!generated_once}) for each of [elements], each with the entity it
    falls back to ({!funs_entities}), as one group to finish later
    ({!finalized}). *)
val functions_ahead : (Names.GlobRef.t * Gen_decls.generated_fun list) list -> ahead

(** [entity r ids helpers] is the generation of [r]: the declarations
    [ids], and the helpers among [helpers]. *)
val entity :
  Names.GlobRef.t -> Unit_program.id list -> Minicpp.cpp_decl list -> Unit_program.entity

(** [funs_entities ~fallback funs] is each generated function as the entity
    its declaration is about, [fallback] where it says none. *)
val funs_entities :
  fallback:Names.GlobRef.t -> Gen_decls.generated_fun list -> Unit_program.entity list

(** Generate, ahead of both files, what the declaration [d] is written as
    that {!impl_decls} and {!header_decls} then take from here: its
    functions ({!generated_once}), the struct of the instance it is
    ({!instance_entity}), or what the header alone writes of it, generated in
    the scope the header writes it in ({!header_scope}); and say what of it
    to finish. *)
val generate_ahead : module_:Names.ModPath.t -> Miniml.ml_decl -> ahead

(** How the header writes a module's body: inside a struct or not, and with
    the module's class concepts already declared ahead of its struct or not,
    which is all generating a declaration asks of where it is written.
    Planned for every module ahead of the files ({!plan_header_scope}) and
    checked against the header's render context as it enters the module. *)
type header_scope = {
  in_struct : bool;  (** The body is written inside a struct. *)
  concepts_hoisted : bool;
      (** The module's class concepts are declared ahead of its struct, so
          the body does not declare them again. *)
}

(** [plan_header_scope mp scope] plans [scope] for the body of the module
    [mp]. *)
val plan_header_scope : Names.ModPath.t -> header_scope -> unit

(** The scope planned for the body of a module. *)
val header_scope : Names.ModPath.t -> header_scope option

(** [spelling_position ~file spelling] is the position a declaration
    spelled [spelling] is written at in [file], a function of the plan
    alone. *)
val spelling_position : file:Common.file -> Cpp_ast.spelling -> Cpp_state.render_ctx

(** A group of finished declarations the header writes at file scope, away
    from the module [source] they were generated in.  They are spelled as
    the header spells an element of [source] -- in the visibility planned
    for its body, with the inductives it spells bare, and in its planned
    header scope -- so the module is all a group has to say about where it
    reads its names from. *)
type group = {source : Names.ModPath.t; declarations : rendered}

(** Groups in writing order. *)
type section = group list

(** A section's groups, in order, written at the position given, each to be
    printed as an element of its source module is spelled
    ({!Cpp_ast.Elements}). *)
val render_section : Cpp_state.render_ctx -> section -> Cpp_ast.t list

(** [resolver_at ~file spelling] names what a declaration spelled
    [spelling] names where it is written in [file], in the visibility planned
    there, at a frame inside it ({!Cpp_ast.resolve}). *)
val resolver_at : file:Common.file -> Cpp_ast.spelling -> Cpp_ast.resolver

(** {!Cpp_ast.resolve_tree} by {!resolver_at}, a declaration naming what
    {!Cpp_leaf_plan.unprinted_names} and {!Cpp_concepts.names_requested} say,
    for a question about [t] rather than to write it: nothing it names is
    noted as written ({!Common.check_written_files}). *)
val resolve_tree : file:Common.file -> Cpp_ast.t -> Cpp_ast.t

(** {!Cpp_ast.resolve} as {!resolve_tree} resolves each section, to write
    it: what a struct's head names is noted as written. *)
val resolve : file:Common.file -> Cpp_ast.scheduled -> Cpp_ast.scheduled

(** {!Cpp_leaf_plan.resolved_names_into_a_struct} of a declaration as [file]
    writes it spelled [spelling]: at the position printing it is at, and of
    the names resolution settles there ({!resolver_at}), which are the ones
    printing it reads. *)
val names_into_a_struct_as_written : file:Common.file -> Cpp_ast.spelling -> Cpp_ir.Resolved.Decl.t -> bool option

(** Print a declaration not yet printed as the tree spells it
    ({!Cpp_ast.print}). *)
val write_unprinted : file:Common.file -> Cpp_ast.spelling -> Cpp_ast.unprinted -> Pp.t

(** Where the header declares one of a module's concepts.  No concept can
    be declared inside a struct, so a module nested in one declares its
    concepts at file scope.  Otherwise a concept goes ahead of the module's
    struct, whose body may constrain a functor with it, unless it names one
    of the struct's members, when it follows the struct. *)
type concept_placement = Cpp_state.concept_placement = Ahead_of_struct | After_struct | At_file_scope

(** {!Cpp_state.concept_plan}. *)
type concept_plan = Cpp_state.concept_plan = {
  placements : (Cpp_state.held_concept * concept_placement) list;
      (** The class concepts, then the module-type concepts, in declaration
          order. *)
  held_back : Cpp_state.held_concept list;
      (** The concepts the struct's body treats as not declared yet. *)
}

(** [plan_concepts ~nested ~classes ~modtypes] places the concepts
    [classes] and then [modtypes], each with whether it names a member of
    its module, of a module inside a struct if [nested]. *)
val plan_concepts :
  nested:bool ->
  classes:(Cpp_state.held_concept * bool) list ->
  modtypes:(Cpp_state.held_concept * bool) list ->
  concept_plan

(** Structural equality of two plans, placements in order. *)
val equal_concept_plan : concept_plan -> concept_plan -> bool

(** Where [plan] places the concept [c]; an anomaly if it does not. *)
val concept_placement : concept_plan -> Cpp_state.held_concept -> concept_placement

(** [concept r fields] is the concept of the class [r], of fields [fields]:
    generated ahead of the files ({!generating_ahead}) in the module
    declaring the class, and taken from there by the header, which generates
    it again under [CRANE_CHECK_IR] to compare. *)
val concept : module_:Names.ModPath.t -> Names.GlobRef.t -> Miniml.record_field list -> Minicpp.cpp_decl

(** [modtype_concept path ~params mt] is the concept of the module type [mt]
    at [path], over the functor parameters [params]: generated ahead of the
    files where the header writes it, and taken from there by the header,
    which generates it again under [CRANE_CHECK_IR] to compare. *)
val modtype_concept :
  module_:Names.ModPath.t -> Names.ModPath.t -> params:Names.ModPath.t list -> Miniml.ml_module_type -> Modtype_concept.t

(** [record_methods r vars candidates] is the methods the eponymous record
    [r], of variables [vars], is given, made of [candidates], with the
    helpers lifted out of them: generated ahead of the files, and taken from
    there by the header, which generates them again under [CRANE_CHECK_IR]
    to compare. *)
val record_methods :
  module_:Names.ModPath.t ->
  Names.GlobRef.t ->
  Names.Id.t list ->
  Method_registry.method_candidate list ->
  (Minicpp.cpp_field * Minicpp.cpp_visibility * Minicpp.section_tag) list * Minicpp.cpp_decl list

(** [record_field_types r vars fields] is the C++ type of each of the
    fields [fields] of the eponymous record [r], of variables [vars], which
    the header writes in the struct [r] is merged into, in CppIR: converted
    ahead of the files, and taken from there by the header, which converts
    them again under [CRANE_CHECK_IR] to compare. *)
val record_field_types :
  module_:Names.ModPath.t -> Names.GlobRef.t -> Names.Id.t list -> Miniml.record_field list -> Cpp_ir.Resolved.Type.t list

(** Every module type's concept generated ahead of the files
    ({!modtype_concept}). *)
val generated_concepts : unit -> Modtype_concept.t list

(** The types of every eponymous record's fields converted ahead of the
    files ({!record_field_types}). *)
val generated_record_field_types : unit -> Cpp_ir.Resolved.Type.t list

(** [record_methods_finishing r vars fields] is what finishing [fields],
    the methods of the eponymous record [r] of variables [vars], takes: the
    members of its module's struct, as the owner's methods
    ({!Unit_program.Methods}). *)
val record_methods_finishing :
  Names.GlobRef.t ->
  Names.Id.t list ->
  (Minicpp.cpp_field * Minicpp.cpp_visibility * Minicpp.section_tag) list ->
  Unit_program.job

(** [finished_record_methods r vars fields] is {!record_methods_finishing}
    finished ahead of the files, taken from there by the header. *)
val finished_record_methods :
  Names.GlobRef.t ->
  Names.Id.t list ->
  (Minicpp.cpp_field * Minicpp.cpp_visibility * Minicpp.section_tag) list ->
  Cpp_ir.Resolved.Decl.t

(** [regenerating f] runs [f], generating again what was generated ahead
    of the files to check it: {!generated_once} and {!instance_entity}
    compare what they generate with what they recorded, and record and claim
    nothing. *)
val regenerating : (unit -> 'a) -> 'a

(** [peeking f] runs [f], reading what was generated ahead of the files to
    plan what they will write of it: what {!generated_once},
    {!instance_entity} and the other generators recorded is handed out
    without being taken -- nothing is recorded, claimed or deferred --
    and a lifted helper's placement is the planned one. *)
val peeking : (unit -> 'a) -> 'a

(** [regenerate_ahead d] generates again what {!generate_ahead} generated
    for [d], checking it ({!regenerating}). *)
val regenerate_ahead : module_:Names.ModPath.t -> Miniml.ml_decl -> unit

(** [finished_placed (id, d)] is [d], the declaration [id] placed beside
    the generation it was lifted out of or handed on with, as the unit's
    program has it ({!Unit_program}).  That the program does not have it
    is an anomaly; a file's pass finishes it again under [CRANE_CHECK_IR]
    and checks.  So for every [finished_] reader below. *)
val finished_placed : Unit_program.id * Minicpp.cpp_decl -> Cpp_ir.Resolved.Decl.t

(** [finished_helper d] is the lifted helper [d] ({!finished_placed} under
    its {!helper_id}). *)
val finished_helper : Minicpp.cpp_decl -> Cpp_ir.Resolved.Decl.t

(** [entity_placed (id, d)] is the function entity of {!finished_placed}:
    its declaration and definition. *)
val entity_placed : Unit_program.id * Minicpp.cpp_decl -> Function_entity.t

(** [helper_entity d] is {!entity_placed} of the lifted helper [d] under
    its {!helper_id}. *)
val helper_entity : Minicpp.cpp_decl -> Function_entity.t

(** [finished_concept r d] is [d], the concept of the class [r]. *)
val finished_concept : Names.GlobRef.t -> Minicpp.cpp_decl -> Cpp_ir.Resolved.Decl.t

(** [finished_declared ~fallback g d] is [d], the declaration without a
    definition that the generated function [g] is, [fallback] the entity it
    falls back to ({!funs_entities}). *)
val finished_declared :
  fallback:Names.GlobRef.t -> Gen_decls.generated_fun -> Minicpp.cpp_decl -> Cpp_ir.Resolved.Decl.t

(** A generated function, finished: a definition, with the file holding it
    and its entity, made of the definition as the unit's program has it; or
    a declaration with no definition anywhere. *)
type finished_fun =
  | Finished_definition of Gen_decls.definition_file * Function_entity.t
  | Finished_declaration of Minicpp.cpp_decl

(** [finalized ~fallback funs] pairs each generated function with what it
    finishes as.  [fallback] is the entity a function falls back to
    ({!funs_entities}). *)
val finalized :
  fallback:Names.GlobRef.t ->
  Gen_decls.generated_fun list ->
  (Gen_decls.generated_fun * finished_fun) list

(** The kinds of the template parameters of every inductive and type alias
    [struc] declares, decided before anything is generated: a use converted
    ahead of the declaration passes what its definition declares.  Decided in
    declaration order, each recorded as it is: an alias's kinds come out of
    its converted body, which reads the kinds of the declarations it names. *)
val template_kinds : Miniml.ml_structure -> (Names.GlobRef.t * Tparam_kinds.t) list

(** {2 Recording the generated program}

    What the printer renders is recorded in {!Unit_program} as it is
    generated. *)

(** [record_entity r ids helpers] records that generating the source
    entity [r] gave the declarations [ids] to finish and lifted
    [helpers]. *)
val record_entity :
  Names.GlobRef.t -> Unit_program.id list -> Minicpp.cpp_decl list -> Unit_program.entity

(** [record_funs ~fallback funs] records each generated function as the
    entity its declaration is about, [fallback] where it names none. *)
val record_funs : fallback:Names.GlobRef.t -> Gen_decls.generated_fun list -> unit

(** [instance_entity r a t] is the instance [r], of body [a] and type [t]
    ({!instance_decls}), recorded as the entity [r], with the helpers lifted
    out of its methods, which come before it.  Generated ahead of the files
    ({!generating_ahead}) and taken from there by the header; that it was
    not is an anomaly.  [CRANE_CHECK_IR] regenerates and checks. *)
val instance_entity :
  module_:Names.ModPath.t -> Names.GlobRef.t -> Miniml.ml_ast -> Miniml.ml_type -> generated * Minicpp.cpp_decl list

(** What a file writes for one MiniML declaration, and the helpers lifted
    out of it that the element places: a constant's or a function's.  A
    fixpoint's helpers are written in front of it, and are not among them. *)
type element = {
  rendered : rendered;  (** The declarations written, finished. *)
  helpers : Minicpp.cpp_decl list;
      (** The lifted helpers this element places; empty where the header
          writes them in front of each function, or writes none. *)
  member_defs : rendered;
      (** The definitions of members its struct gave up, written at the end
          of the file: only a datatype's, and only in the header. *)
}

(** The implementation-file declarations for one MiniML declaration, written
    at the position given. *)
val impl_decls : Cpp_state.render_ctx -> module_:Names.ModPath.t -> Miniml.ml_decl -> element

(** The header declarations for one MiniML declaration, written at the
    position given. *)
val header_decls : Cpp_state.render_ctx -> module_:Names.ModPath.t -> Miniml.ml_decl -> element

(** What {!header_decls} gives for a declaration, read off what was generated
    ahead of the files without taking it: nothing is recorded or claimed,
    and the helpers are those the header is planned to place there.  Read
    at the position given. *)
val header_element_ahead : Cpp_state.render_ctx -> module_:Names.ModPath.t -> Miniml.ml_decl -> element

(** What the implementation writes for a declaration, read off what was
    generated ahead of the files without taking it, at the position
    given. *)
val impl_element_ahead : Cpp_state.render_ctx -> module_:Names.ModPath.t -> Miniml.ml_decl -> element

(** Whether the inductive [d] declares, promoted to its module's struct,
    makes that struct derive from [enable_shared_from_this], read off what
    was generated ahead of the files in the module [module_], written at
    the position given. *)
val promoted_shared_from_this : Cpp_state.render_ctx -> module_:Names.ModPath.t -> Miniml.ml_decl -> bool

