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

(** {1 Extraction from Rocq Terms to MiniML}

    First stage of the extraction pipeline:
    {v Rocq CIC  --[extraction.ml]-->  MiniML AST v}

    Converts Rocq's Calculus of Inductive Constructions into a
    simply-typed functional language ({!Miniml}).  This step performs
    type erasure (removing propositions, universe levels, implicit
    arguments) and computes signatures tracking which arguments survive
    extraction ([Keep]/[Kill]). *)

open Names
open Declarations
open Environ
open Evd
open Miniml

val extract_constant : Global.indirect_accessor -> env -> Constant.t -> constant_body -> ml_decl
(** Extract a single constant definition into an ML declaration. *)

val extract_constant_spec : env -> Constant.t -> ('a, 'b) pconstant_body -> ml_spec
(** Extract the type signature of a constant (for module signatures). *)

val extract_with_type :
  env -> evar_map -> EConstr.t -> ( Id.t list * ml_type ) option
(** Extract a [module ... with Definition ... := ...] constraint. *)

val extract_fixpoint :
  env -> evar_map -> Constant.t array -> EConstr.rec_declaration -> ml_decl
(** Extract a mutual fixpoint definition. *)

val extract_inductive : env -> MutInd.t -> ml_ind
(** Extract a (mutual) inductive type definition. *)

val extract_constr : env -> evar_map -> EConstr.t -> ml_ast * ml_type
(** Extract a single term (for [Extraction Compute] and [Show Extraction]). *)

val logical_decl : ml_decl -> bool
(** Is the declaration purely logical (erased during extraction)? *)

val logical_spec : ml_spec -> bool
(** Is the specification purely logical? *)
