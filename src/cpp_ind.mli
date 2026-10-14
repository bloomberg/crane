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

(** [generated_once ?on_reuse node gen] is [gen ()], except that the header
    pass reuses what the implementation pass generated from the physical
    MiniML node [node] in the same render context and module -- emission
    decides nothing after discovery, so the two agree -- handing it to
    [on_reuse] to replay any effect generating it had.  [CRANE_CHECK_IR]
    regenerates and checks. *)
val generated_once :
  ?on_reuse:(Gen_decls.generated_fun list -> unit) ->
  'node ->
  (unit -> Gen_decls.generated_fun list) ->
  Gen_decls.generated_fun list

(** [finalized funs] pairs each generated function with its entity, every
    definition among them finished as one group
    ({!Function_entity.finalize_group}); [None] for a declaration. *)
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

