(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The C++ concept a module type becomes ({!Modtype_concept.t}), as text:
    its declaration, the concepts of the module types nested in it, and the
    name every reference to it spells.  Part of the printer: the concept
    itself is built by {!Modtype_concept}, and the names it writes are
    resolved ahead of printing from {!names_requested}. *)

open Names

(** [pp_modtype_concept ctx ~names ~params path c] is the declaration, at
    the position [ctx], of the concept of the module type at [path],
    generated as [c], over [M] and the parameters [params] of a functor
    declaring it, with the concepts its nested module types are hoisted into
    ahead of it, naming what [names] names ({!names_requested}). *)
val pp_modtype_concept :
  Cpp_state.render_ctx ->
  names:Cpp_resolution.table ->
  params:ModPath.t list ->
  ModPath.t ->
  Modtype_concept.t ->
  Pp.t

(** The assertion [a], as written at the position where the tree puts it. *)
val pp_assertion : Cpp_state.render_ctx -> Cpp_ast.assertion -> Pp.t

(** What a declaration not yet printed names, at the frames inside it,
    beyond the references the tree holds itself: what
    {!Cpp_ast.resolve_tree} resolves into its table.  Of a module type's
    concept, every name its declaration writes, the globals of the types it
    writes included ({!Cpp_leaf_plan.global_names}); of any other
    declaration, nothing. *)
val names_requested : Cpp_ast.declaration -> (Cpp_resolution.frame * Cpp_resolution.key) list

(** What the definition of the concept [c] names after its head, at the
    frames inside it: the base concept it refines, the modules that concept
    is applied to past [M] and the globals of the refinements' types, or its
    requirements' names. *)
val concept_body_names : Modtype_concept.t -> (Cpp_resolution.frame * Cpp_resolution.key) list
