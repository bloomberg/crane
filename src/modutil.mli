(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(** {1 ML Module Utilities}

    Traversal, search, and optimization functions over the Core module
    structure ({!Core.Program.t}).  {!optimize_struct} is the
    simplification and dead-code pass extraction runs on the structure before
    it reaches the backend; the iterators and maps are shared by every later
    pass that walks a structure. *)

(** Search for an AST node satisfying a predicate anywhere in the structure.
    @param f predicate to test each [Core.Expr.t] node
    @return [true] if any node satisfies [f], [false] otherwise *)
val struct_ast_search : (Core.Expr.t -> bool) -> Core.Program.t -> bool

(** Search for a type satisfying a predicate anywhere in the structure.
    @param f predicate tested on each leaf type: a node that is neither an
      arrow nor a [Core.Type.Global_app], whose arguments are searched instead
    @return [true] if any type satisfies [f], [false] otherwise *)
val struct_type_search : (Core.Type.t -> bool) -> Core.Program.t -> bool

(** Every function the structure defines outside a functor, with its body
    and type: a constant whose body is a lambda, and each member of a
    recursive group. *)
val struct_functions : Core.Program.t -> (GlobRef.t * Core.Expr.t * Core.Type.t) list

(** Iterate over all declarations, specifications, and module paths, in
    module and functor bodies and module types alike.
    @param do_decl callback invoked for each [Core.Decl.t] found
    @param do_spec callback invoked for each [Core.Signature.Declaration.t] found
    @param do_mp callback invoked for each [ModPath.t] found *)
val struct_iter :
  (Core.Decl.t -> unit) ->
  (Core.Signature.Declaration.t -> unit) ->
  (ModPath.t -> unit) ->
  Core.Program.t ->
  unit

(** Callback applied to each global reference encountered by the
    reference-traversal iterators below ({!type_iter_references},
    {!ast_iter_references}, and friends). *)
type do_ref = GlobRef.t -> unit

(** Apply [do_ref] to every [GlobRef.t] in an ML type.
    @param do_ref callback invoked for each global reference encountered
    @param t the type to traverse *)
val type_iter_references : do_ref -> Core.Type.t -> unit

(** [ast_iter_references do_term do_cons do_type ast] applies the appropriate
    callback to every reference in [ast].
    @param prune when [prune a] is [true], [a] is skipped entirely: neither its
      own references nor those of its subterms are visited (used to drop subtrees
      that later passes fold away, e.g. numeral-converter applications)
    @param do_term callback for term-level references ([Core.Expr.Global])
    @param do_cons callback for constructor references ([Core.Expr.Construct], [Core.Pattern.Constructor])
    @param do_type callback for type-level references ([Core.Type.Global_app]) *)
val ast_iter_references :
  ?prune:(Core.Expr.t -> bool) -> do_ref -> do_ref -> do_ref -> Core.Expr.t -> unit

(** Like {!ast_iter_references} but for declarations.
    @param prune see {!ast_iter_references}
    @param do_term callback for term-level references
    @param do_cons callback for constructor references
    @param do_type callback for type-level references *)
val decl_iter_references :
  ?prune:(Core.Expr.t -> bool) -> do_ref -> do_ref -> do_ref -> Core.Decl.t -> unit

(** Like {!ast_iter_references} but for specifications.
    @param do_term callback for term-level references
    @param do_cons callback for constructor references
    @param do_type callback for type-level references *)
val spec_iter_references : do_ref -> do_ref -> do_ref -> Core.Signature.Declaration.t -> unit

(** Extract the type signature from a module structure. *)
val signature_of_structure : Core.Program.t -> Core.Interface.t

(** Convert a module expression to its module type. *)
val mtyp_of_mexpr : Core.Module.Expr.t -> Core.Module.Type.t

(** Extract the module path from a module type. *)
val msid_of_mt : Core.Module.Type.t -> ModPath.t

(** Look up a declaration by its [GlobRef.t] in the structure.
    @param r the global reference to look up
    @raise Not_found if the reference is not in the structure. *)
val get_decl_in_structure : GlobRef.t -> Core.Program.t -> Core.Decl.t

(** [decl_of_term r a t] is the declaration of [r], with body [a] and type
    [t]: a fixpoint when [a] is one under its lambdas -- the fixpoint's own
    name becoming [r], its parameters [r]'s -- and a term otherwise. *)
val decl_of_term : GlobRef.t -> Core.Expr.t -> Core.Type.t -> Core.Decl.t

(** Simplify the structure: beta-iota reduction, dead code elimination, inlining
    of singly-used let-bindings. The first argument specifies which definitions
    must be kept (not eliminated).
    @param to_appear pair of global references and module paths that must be
      preserved (not eliminated by dead-code removal)
    @return the optimized structure *)
val optimize_struct :
  GlobRef.t list * ModPath.t list -> Core.Program.t -> Core.Program.t

(** The references a declaration defines; an inductive block is represented
    by its first packet. *)
val declared_refs : Core.Decl.t -> GlobRef.t list

(** [map_struct_decls f s] applies [f] to every declaration of [s], in modules
    and functor bodies alike. *)
val map_struct_decls : (Core.Decl.t -> Core.Decl.t) -> Core.Program.t -> Core.Program.t

(** [map_struct ~spec ~with_type decl s] is {!map_struct_decls}[ decl s] with
    the module types rewritten as well: [spec] applied to every
    specification, and [with_type] to the type each [with] refinement
    fixes. *)
val map_struct :
  ?spec:(Core.Signature.Declaration.t -> Core.Signature.Declaration.t) ->
  ?with_type:(Core.Type.t -> Core.Type.t) ->
  (Core.Decl.t -> Core.Decl.t) ->
  Core.Program.t ->
  Core.Program.t
