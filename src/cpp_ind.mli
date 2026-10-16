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

(** Declarations finished for the printer ({!Cpp_pipeline.finish_group} of
    what one MiniML declaration became). *)
type rendered = (Common.env * Cpp_erasure.settled) list

(** [render_decl env d] finishes [d] and prints it: the one place a generated
    declaration crosses from the compiler's passes to the printer. *)
val render_decl : Common.env -> Minicpp.cpp_decl -> Pp.t

(** Print the declarations an entry point answered with. *)
val pp_decls : rendered -> Pp.t

(** Finished declarations written later than they were generated, each group
    kept with the scope it was generated in ({!Cpp_state.scope}) and rendered
    in it. *)
type deferred

(** [deferred name] is a new, empty band, emptied between extractions and
    reported to the table census under [name]. *)
val deferred : string -> deferred

(** [defer band ds] keeps [ds] in [band], with the current scope. *)
val defer : deferred -> rendered -> unit

(** Render [band]'s groups, in the order they were deferred and each in its
    own scope, and empty it. *)
val render_deferred : deferred -> Pp.t list

(** Empty [band] without rendering it. *)
val discard : deferred -> unit

(** Member definitions a datatype struct at namespace scope gave up because
    their bodies name a module's struct, which is emitted after every datatype
    and cannot be moved in front of one it holds by value.  The header
    assembly writes them last. *)
val deferred_member_defs : deferred

(** File-scope [using X = std::any;] landing pads for erasure, written before
    everything else in the header. *)
val file_scope_erased_aliases : deferred

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

(** [generated_once ?on_reuse node gen] is [gen ()] ahead of the files
    ({!generating_ahead}), recorded by the physical MiniML node [node] and
    the module it is generated in.  A file's pass takes what was recorded
    there -- emission decides nothing the plan has not, so it is what the
    pass would generate -- handing it to [on_reuse] to replay any effect
    generating it had; that nothing was is an anomaly.  [CRANE_CHECK_IR]
    regenerates and checks. *)
val generated_once :
  ?on_reuse:(Gen_decls.generated_fun list -> unit) ->
  'node ->
  (unit -> Gen_decls.generated_fun list) ->
  Gen_decls.generated_fun list

(** [generating_ahead f] runs [f], a walk generating every function before
    either file is rendered, recording what {!generated_once} generates in
    it for both files. *)
val generating_ahead : (unit -> 'a) -> 'a

(** Generate, ahead of both files, what the declaration [d] is written as
    that {!impl_decls} and {!header_decls} then take from here: its
    functions, generated ({!generated_once}) and finished ({!finalized}),
    or the struct of the instance it is ({!instance_entity}); and return the
    helpers lifted out of them.  Nothing for any other declaration. *)
val generate_ahead : Miniml.ml_decl -> Minicpp.cpp_decl list

(** [regenerating f] runs [f], generating again what was generated ahead
    of the files to check it: {!generated_once} and {!instance_entity}
    compare what they generate with what they recorded, and record and claim
    nothing. *)
val regenerating : (unit -> 'a) -> 'a

(** [regenerate_ahead d] generates again what {!generate_ahead} generated
    for [d], checking it ({!regenerating}). *)
val regenerate_ahead : Miniml.ml_decl -> unit

(** [finished_alone d] is [d] finished on its own ({!Cpp_pipeline.finish}):
    a declaration written without a definition, or a lifted helper.  Ahead
    of the files ({!generating_ahead}) it is finished and recorded; a file's
    pass takes it from there, and finds it missing only as an anomaly.
    [CRANE_CHECK_IR] finishes again and checks. *)
val finished_alone : Minicpp.cpp_decl -> Cpp_erasure.settled

(** [finalized funs] pairs each generated function with its entity, every
    definition among them finished as one group
    ({!Function_entity.finalize_group}); [None] for a declaration.  Finished
    ahead of the files ({!generating_ahead}) and taken from there by a
    file's pass; that it was not is an anomaly.  [CRANE_CHECK_IR] finishes
    again and checks. *)
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

(** [generated_entity r ds] runs the generation [ds], recording what it
    produced and the helpers it lifted as the entity [r], and returns both:
    the helpers are the caller's to place. *)
val generated_entity :
  Names.GlobRef.t -> (unit -> generated) -> generated * Minicpp.cpp_decl list

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
}

(** The implementation-file declarations for one MiniML declaration. *)
val impl_decls : Miniml.ml_decl -> element

(** The header declarations for one MiniML declaration. *)
val header_decls : Miniml.ml_decl -> element

