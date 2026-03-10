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

    Traversal, search, and optimization functions over the MiniML
    module structure ({!Miniml.ml_structure}). *)

open Names
open Miniml

val struct_ast_search : (ml_ast -> bool) -> ml_structure -> bool
(** Search for an AST node satisfying a predicate anywhere in the structure. *)

val struct_type_search : (ml_type -> bool) -> ml_structure -> bool
(** Search for a type satisfying a predicate anywhere in the structure. *)

val struct_iter :
  (ml_decl -> unit) -> (ml_spec -> unit) -> (ModPath.t -> unit) ->
  ml_structure -> unit
(** Iterate over all declarations, specifications, and module paths. *)

type do_ref = GlobRef.t -> unit

val type_iter_references : do_ref -> ml_type -> unit
(** Apply [do_ref] to every [GlobRef.t] in an ML type. *)

val ast_iter_references : do_ref -> do_ref -> do_ref -> ml_ast -> unit
(** [ast_iter_references do_type do_cons do_term ast] applies the
    appropriate callback to every reference in [ast]. *)

val decl_iter_references : do_ref -> do_ref -> do_ref -> ml_decl -> unit
(** Like {!ast_iter_references} but for declarations. *)

val spec_iter_references : do_ref -> do_ref -> do_ref -> ml_spec -> unit
(** Like {!ast_iter_references} but for specifications. *)

val signature_of_structure : ml_structure -> ml_signature
(** Extract the type signature from a module structure. *)

val mtyp_of_mexpr : ml_module_expr -> ml_module_type
(** Convert a module expression to its module type. *)

val msid_of_mt : ml_module_type -> ModPath.t
(** Extract the module path from a module type. *)

val get_decl_in_structure : GlobRef.t -> ml_structure -> ml_decl
(** Look up a declaration by its [GlobRef.t] in the structure.
    @raise Not_found if the reference is not in the structure. *)

val optimize_struct : GlobRef.t list * ModPath.t list ->
  ml_structure -> ml_structure
(** Simplify the structure: beta-iota reduction, dead code elimination,
    inlining of singly-used let-bindings.  The first argument specifies
    which definitions must be kept (not eliminated). *)
