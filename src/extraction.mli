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

    Converts Rocq's Calculus of Inductive Constructions into a simply-typed
    functional language ({!Miniml}). This step performs type erasure (removing
    propositions, universe levels, implicit arguments) and computes signatures
    tracking which arguments survive extraction ([Keep]/[Kill]). *)

open Names
open Declarations
open Environ
open Evd
open Miniml

(** Extract a single constant definition into an ML declaration.
    @param access Indirect accessor used to force opaque proof bodies when [access_opaque ()] is set
    @param env Rocq global environment
    @param kn The constant name to extract
    @param cb The constant body (declaration) from the environment *)
val extract_constant :
  Global.indirect_accessor -> env -> Constant.t -> constant_body -> ml_decl

(** Extract the type signature of a constant (for module signatures).
    @param env Rocq global environment
    @param kn The constant name whose spec is extracted
    @param cb The constant body; only its type is used (the body is inspected for [Def] to produce an abbreviation) *)
val extract_constant_spec :
  env -> Constant.t -> ('a, 'b) pconstant_body -> ml_spec

(** Extract a [module ... with Definition ... := ...] constraint.
    @param env Rocq global environment
    @param sg Evar map for universe and constraint tracking
    @param c The constrained term (right-hand side of the [with] clause)
    @return [Some (vars, ty)] if [c] is an informative type scheme, [None] if logical *)
val extract_with_type :
  env -> evar_map -> EConstr.t -> (Id.t list * ml_type) option

(** Extract a mutual fixpoint definition. The bool parameter indicates whether
    it's a regular fixpoint (true) or a cofixpoint (false).
    @param env Rocq global environment
    @param sg Evar map for universe and constraint tracking
    @param vkn Array of constant names for each mutually recursive component
    @param is_fix [true] for a regular fixpoint, [false] for a cofixpoint
    @param recd The raw recursive declaration ([fi], [ti], [ci]) from the kernel *)
val extract_fixpoint :
  env ->
  evar_map ->
  Constant.t array ->
  bool ->
  EConstr.rec_declaration ->
  ml_decl

(** Extract a (mutual) inductive type definition. *)
val extract_inductive : env -> MutInd.t -> ml_ind

(** Extract a single term (for [Extraction Compute] and [Show Extraction]).
    @param env Rocq global environment
    @param sg Evar map for universe and constraint tracking
    @param c The term to extract
    @return A pair [(ast, ty)] of the extracted ML expression and its ML type *)
val extract_constr : env -> evar_map -> EConstr.t -> ml_ast * ml_type

(** Is the declaration purely logical (erased during extraction)? *)
val logical_decl : ml_decl -> bool

(** Is the specification purely logical? *)
val logical_spec : ml_spec -> bool
