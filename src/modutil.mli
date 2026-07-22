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
open Miniml

(** {1 ML Module Utilities}

    Traversal, search, and optimization functions over the MiniML module
    structure ({!Miniml.ml_structure}). *)

(** Search for an AST node satisfying a predicate anywhere in the structure.
    @param f predicate to test each [ml_ast] node
    @param the structure to search
    @return [true] if any node satisfies [f], [false] otherwise *)
val struct_ast_search : (ml_ast -> bool) -> ml_structure -> bool

(** Search for a type satisfying a predicate anywhere in the structure.
    @param f predicate to test each [ml_type] node
    @return [true] if any type satisfies [f], [false] otherwise *)
val struct_type_search : (ml_type -> bool) -> ml_structure -> bool

(** Iterate over all declarations, specifications, and module paths.
    @param do_decl callback invoked for each [ml_decl] found
    @param do_spec callback invoked for each [ml_spec] found
    @param do_mp callback invoked for each [ModPath.t] found *)
val struct_iter :
  (ml_decl -> unit) ->
  (ml_spec -> unit) ->
  (ModPath.t -> unit) ->
  ml_structure ->
  unit

type do_ref = GlobRef.t -> unit

(** Apply [do_ref] to every [GlobRef.t] in an ML type.
    @param do_ref callback invoked for each global reference encountered
    @param t the type to traverse *)
val type_iter_references : do_ref -> ml_type -> unit

(** [ast_iter_references do_term do_cons do_type ast] applies the appropriate
    callback to every reference in [ast].
    @param prune when [prune a] is [true], [a] is skipped entirely — neither its
      own references nor those of its subterms are visited (used to drop subtrees
      that later passes fold away, e.g. numeral-converter applications)
    @param do_term callback for term-level references ([MLglob])
    @param do_cons callback for constructor references ([MLcons], [Pcons])
    @param do_type callback for type-level references ([Tglob]) *)
val ast_iter_references :
  ?prune:(ml_ast -> bool) -> do_ref -> do_ref -> do_ref -> ml_ast -> unit

(** Like {!ast_iter_references} but for declarations.
    @param prune see {!ast_iter_references}
    @param do_term callback for term-level references
    @param do_cons callback for constructor references
    @param do_type callback for type-level references *)
val decl_iter_references :
  ?prune:(ml_ast -> bool) -> do_ref -> do_ref -> do_ref -> ml_decl -> unit

(** Like {!ast_iter_references} but for specifications.
    @param do_term callback for term-level references
    @param do_cons callback for constructor references
    @param do_type callback for type-level references *)
val spec_iter_references : do_ref -> do_ref -> do_ref -> ml_spec -> unit

(** Extract the type signature from a module structure. *)
val signature_of_structure : ml_structure -> ml_signature

(** Convert a module expression to its module type. *)
val mtyp_of_mexpr : ml_module_expr -> ml_module_type

(** Extract the module path from a module type. *)
val msid_of_mt : ml_module_type -> ModPath.t

(** Look up a declaration by its [GlobRef.t] in the structure.
    @param r the global reference to look up
    @param the structure to search
    @raise Not_found if the reference is not in the structure. *)
val get_decl_in_structure : GlobRef.t -> ml_structure -> ml_decl

(** Simplify the structure: beta-iota reduction, dead code elimination, inlining
    of singly-used let-bindings. The first argument specifies which definitions
    must be kept (not eliminated).
    @param to_appear pair of global references and module paths that must be
      preserved (not eliminated by dead-code removal)
    @return the optimized structure *)
val optimize_struct :
  GlobRef.t list * ModPath.t list -> ml_structure -> ml_structure
