(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Which C++ declarations a MiniML declaration becomes.

   This module turns MiniML inductives ([ml_ind]) and declarations
   ([ml_decl]/[ml_spec]) into {!Minicpp.cpp_decl} values.  It has two families
   of entry points:

   - the source-file family ([impl_decls]) gives the full definitions that
     go into the generated [.cpp]; and
   - the header family ([header_decls])
     gives the declarations that go into the generated [.h].

   Each answer pairs a declaration with the name environment its
   sub-expressions are printed in; {!pp_decls} prints them.

   Everything else in the implementation is an internal helper and is
   deliberately hidden by this interface. *)

(** Declarations as generated, each with the name environment it is printed
    in. *)
type generated = (Common.env * Minicpp.cpp_decl) list

(** Declarations finished for the printer ({!Cpp_pipeline.finish} of what
    one MiniML declaration became). *)
type rendered = (Common.env * Cpp_erasure.settled) list

(** [render_decl env d] prints [d] as it was finished ahead of the files
    ({!finished_alone}). *)
val render_decl : Common.env -> Minicpp.cpp_decl -> Cpp_ast.t

(** Print the declarations an entry point answered with. *)
val pp_decls : rendered -> Cpp_ast.t

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

(** [generated_once ?on_reuse ?planned node gen] is [gen ()] ahead of the
    files ({!generating_ahead}), recorded by the physical MiniML node [node]
    and the module it is generated in, and handed to [planned] to plan what
    taking it needs.  A file's pass takes what was recorded there --
    emission decides nothing the plan has not, so it is what the pass would
    generate -- handing it to [on_reuse] to replay any effect generating it
    had; that nothing was is an anomaly.  [CRANE_CHECK_IR] regenerates and
    checks.  Read while peeking ({!header_element_ahead}), it is what was
    recorded, handed to [on_peek] in place of [on_reuse]. *)
val generated_once :
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

(** Begin a render of a file: under [CRANE_CHECK_IR] the header claims the
    helpers it places afresh, to check them against the planned claims. *)
val start_render : unit -> unit

(** A declaration to finish ({!Finished_program.job}). *)
type finishing = Finished_program.job

(** [finishing d] is [d] to finish, its result recorded by [d] itself. *)
val finishing : Minicpp.cpp_decl -> finishing


(** What generating a declaration ahead of the files leaves for later: the
    functions it generated, which Loopify reads while finishing any function
    of the unit, so that all are registered before any is finished; what of
    it to finish; and the helpers lifted out of it, finished once everything
    else is. *)
type ahead = {
  entities : Generated_program.entity list;
      (** What was generated, as the entities a file records taking it. *)
  functions : Minicpp.cpp_decl list;
  finishing : finishing list;
  helpers : Minicpp.cpp_decl list;
}

(** [functions_ahead ~entities funs]: [funs], generated ahead
    ({!generated_once}) as [entities], to finish later ({!finalized}). *)
val functions_ahead :
  entities:Generated_program.entity list -> Gen_decls.generated_fun list -> ahead

(** [entity r decls helpers] is the generation of [r]: [decls], and the
    helpers among [helpers]. *)
val entity :
  Names.GlobRef.t -> Minicpp.cpp_decl list -> Minicpp.cpp_decl list -> Generated_program.entity

(** [funs_entities ~fallback funs] is each generated function as the entity
    its declaration is about, [fallback] where it says none. *)
val funs_entities :
  fallback:Names.GlobRef.t -> Gen_decls.generated_fun list -> Generated_program.entity list

(** Generate, ahead of both files, what the declaration [d] is written as
    that {!impl_decls} and {!header_decls} then take from here: its
    functions ({!generated_once}), the struct of the instance it is
    ({!instance_entity}), or what the header alone writes of it, generated in
    the scope the header writes it in ({!header_scope}); and say what of it
    to finish. *)
val generate_ahead : Miniml.ml_decl -> ahead

(** How the header writes a module's body: inside a struct or not, and with
    the module's class concepts already declared ahead of its struct or not.
    Planned for every module ahead of the files ({!plan_header_scope}) and
    checked against the header's render context as it enters the module. *)
type header_scope = {
  in_struct : bool;
  concepts_hoisted : bool;
}

(** [plan_header_scope mp scope] plans [scope] for the body of the module
    [mp]. *)
val plan_header_scope : Names.ModPath.t -> header_scope -> unit

(** The scope planned for the body of a module. *)
val header_scope : Names.ModPath.t -> header_scope option

(** [in_header_element_scope mp k] runs [k ~in_struct] in the render
    context the header writes an element of the module [mp] in, as planned
    ({!header_scope}): [in_struct] says whether that is inside the module's
    struct. *)
val in_header_element_scope : Names.ModPath.t -> (in_struct:bool -> 'a) -> 'a

(** A group of finished declarations the header writes at file scope, away
    from the module [source] they were generated in.  They are spelled as
    the header spells an element of [source] -- in the visibility planned
    for its body and in its planned header scope -- so the module is all a
    group has to say about where it reads its names from. *)
type group = {source : Names.ModPath.t; declarations : rendered}

(** Groups in writing order. *)
type section = group list

(** A section's groups, in order, each to be printed as an element of its
    source module is spelled ({!Cpp_ast.Elements}). *)
val render_section : section -> Cpp_ast.t list

(** Print a declaration not yet printed as the tree spells it
    ({!Cpp_ast.print}). *)
val write_unprinted : Cpp_ast.spelling -> Cpp_ast.unprinted -> Pp.t

(** Where the header declares one of a module's concepts.  No concept can
    be declared inside a struct, so a module nested in one declares its
    concepts at file scope.  Otherwise a concept goes ahead of the module's
    struct, whose body may constrain a functor with it, unless it names one
    of the struct's members, when it follows the struct. *)
type concept_placement = Ahead_of_struct | After_struct | At_file_scope

(** The concepts of a module's classes and module types, planned ahead of
    the files: where each is declared, and which the struct's body treats as
    not declared yet ({!Cpp_state.held_back_concepts}). *)
type concept_plan = {
  placements : (Cpp_state.held_concept * concept_placement) list;
      (** The class concepts, then the module-type concepts, in declaration
          order. *)
  held_back : Cpp_state.held_concept list;
}

(** [plan_concepts ~nested ~classes ~modtypes] places the concepts
    [classes] and then [modtypes], each with whether it names a member of
    its module, of a module inside a struct if [nested]. *)
val plan_concepts :
  nested:bool ->
  classes:(Cpp_state.held_concept * bool) list ->
  modtypes:(Cpp_state.held_concept * bool) list ->
  concept_plan

val equal_concept_plan : concept_plan -> concept_plan -> bool

(** [plan_module_concepts mp plan] plans [plan] for the module [mp]. *)
val plan_module_concepts : Names.ModPath.t -> concept_plan -> unit

(** The concepts planned for the module [mp]; an anomaly if none were. *)
val concept_plan : Names.ModPath.t -> concept_plan

(** Where [plan] places the concept [c]; an anomaly if it does not. *)
val concept_placement : concept_plan -> Cpp_state.held_concept -> concept_placement

(** [concept r fields] is the concept of the class [r], of fields [fields]:
    generated ahead of the files ({!generating_ahead}) in the module
    declaring the class, and taken from there by the header, which generates
    it again under [CRANE_CHECK_IR] to compare. *)
val concept : Names.GlobRef.t -> Miniml.record_field list -> Minicpp.cpp_decl

(** [modtype_concept path ~params mt] is the concept of the module type [mt]
    at [path], over the functor parameters [params]: generated ahead of the
    files where the header writes it, and taken from there by the header,
    which generates it again under [CRANE_CHECK_IR] to compare. *)
val modtype_concept :
  Names.ModPath.t -> params:Names.ModPath.t list -> Miniml.ml_module_type -> Modtype_concept.t

(** [record_methods r vars candidates] is the methods the eponymous record
    [r], of variables [vars], is given, made of [candidates], with the
    helpers lifted out of them: generated ahead of the files, and taken from
    there by the header, which generates them again under [CRANE_CHECK_IR]
    to compare. *)
val record_methods :
  Names.GlobRef.t ->
  Names.Id.t list ->
  Method_registry.method_candidate list ->
  (Minicpp.cpp_field * Minicpp.cpp_visibility * Minicpp.section_tag) list * Minicpp.cpp_decl list

(** [record_field_types r vars fields] is the C++ type of each of the
    fields [fields] of the eponymous record [r], of variables [vars], which
    the header writes in the struct [r] is merged into: converted ahead of
    the files, and taken from there by the header, which converts them again
    under [CRANE_CHECK_IR] to compare. *)
val record_field_types :
  Names.GlobRef.t -> Names.Id.t list -> Miniml.record_field list -> Minicpp.cpp_type list

(** Every module type's concept generated ahead of the files
    ({!modtype_concept}). *)
val generated_concepts : unit -> Modtype_concept.t list

(** The types of every eponymous record's fields converted ahead of the
    files ({!record_field_types}). *)
val generated_record_field_types : unit -> Minicpp.cpp_type list

(** [record_methods_finishing r vars fields] is what finishing [fields],
    the methods of the eponymous record [r] of variables [vars], takes: the
    members of its module's struct, recorded by [fields] itself, as
    {!record_methods} returned it. *)
val record_methods_finishing :
  Names.GlobRef.t ->
  Names.Id.t list ->
  (Minicpp.cpp_field * Minicpp.cpp_visibility * Minicpp.section_tag) list ->
  finishing

(** [finished_record_methods r vars fields] is {!record_methods_finishing}
    finished ahead of the files, taken from there by the header. *)
val finished_record_methods :
  Names.GlobRef.t ->
  Names.Id.t list ->
  (Minicpp.cpp_field * Minicpp.cpp_visibility * Minicpp.section_tag) list ->
  Cpp_erasure.settled

(** [regenerating f] runs [f], generating again what was generated ahead
    of the files to check it: {!generated_once} and {!instance_entity}
    compare what they generate with what they recorded, and record and claim
    nothing. *)
val regenerating : (unit -> 'a) -> 'a

(** [peeking f] runs [f], reading what was generated ahead of the files to
    plan what they will write of it: what {!ahead_once} recorded is handed
    out without being taken -- nothing is recorded, claimed or deferred --
    and a lifted helper's placement is the planned one. *)
val peeking : (unit -> 'a) -> 'a

(** [regenerate_ahead d] generates again what {!generate_ahead} generated
    for [d], checking it ({!regenerating}). *)
val regenerate_ahead : Miniml.ml_decl -> unit

(** [finished_alone d] is [d] finished on its own ({!Cpp_pipeline.finish}):
    a declaration written without a definition, or a lifted helper, as
    the unit's program has it ({!Finished_program}).  That it does not is an anomaly; a file's
    pass finishes it again under [CRANE_CHECK_IR] and checks. *)
val finished_alone : Minicpp.cpp_decl -> Cpp_erasure.settled

(** [finalized funs] pairs each generated function with its entity, made of
    the definition as the unit's program has it; [None] for a declaration.
    That it does not is an anomaly; a file's pass finishes it again under
    [CRANE_CHECK_IR] and checks. *)
val finalized :
  Gen_decls.generated_fun list ->
  (Gen_decls.generated_fun * Function_entity.t option) list

(** The kinds of the template parameters of every inductive and type alias
    [struc] declares, decided before anything is generated: a use converted
    ahead of the declaration passes what its definition declares.  Decided in
    declaration order, each recorded as it is: an alias's kinds come out of
    its converted body, which reads the kinds of the declarations it names. *)
val template_kinds : Miniml.ml_structure -> (Names.GlobRef.t * Tparam_kinds.t) list

(** {2 Recording the generated program}

    What the printer renders is recorded in {!Generated_program} as it is
    generated. *)

(** [record_entity r decls helpers] records that generating the source
    entity [r] produced [decls] and lifted [helpers]. *)
val record_entity :
  Names.GlobRef.t -> Minicpp.cpp_decl list -> Minicpp.cpp_decl list -> Generated_program.entity

(** [record_funs ~fallback funs] records each generated function as the
    entity its declaration is about, [fallback] where it names none. *)
val record_funs : fallback:Names.GlobRef.t -> Gen_decls.generated_fun list -> unit

(** [instance_entity r a t] is the instance [r], of body [a] and type [t]
    ({!instance_decls}), recorded as the entity [r], with the helpers lifted
    out of its methods, which come before it.  Generated ahead of the files
    ({!generating_ahead}) and taken from there by the header; that it was
    not is an anomaly.  [CRANE_CHECK_IR] regenerates and checks. *)
val instance_entity :
  Names.GlobRef.t -> Miniml.ml_ast -> Miniml.ml_type -> generated * Minicpp.cpp_decl list

(** What a file writes for one MiniML declaration, and the helpers lifted
    out of it that the element places: a constant's or a function's.  A
    fixpoint's helpers are written in front of it, and are not among them. *)
type element = {
  rendered : rendered;
  helpers : Minicpp.cpp_decl list;
  member_defs : rendered;
      (** The definitions of members its struct gave up, written at the end
          of the file: only a datatype's, and only in the header. *)
}

(** The implementation-file declarations for one MiniML declaration. *)
val impl_decls : Miniml.ml_decl -> element

(** The header declarations for one MiniML declaration. *)
val header_decls : Miniml.ml_decl -> element

(** What {!header_decls} gives for a declaration, read off what was generated
    ahead of the files without taking it: nothing is recorded or claimed,
    and the helpers are those the header is planned to place there. *)
val header_element_ahead : Miniml.ml_decl -> element

(** What the implementation writes for a declaration, read off what was
    generated ahead of the files without taking it. *)
val impl_element_ahead : Miniml.ml_decl -> element

(** Whether the inductive [d] declares, promoted to its module's struct,
    makes that struct derive from [enable_shared_from_this], read off what
    was generated ahead of the files in the current module. *)
val promoted_shared_from_this : Miniml.ml_decl -> bool

