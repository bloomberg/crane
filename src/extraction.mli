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
    {v Rocq kernel terms  --[extraction.ml]-->  MiniML AST v}

    Converts Rocq terms (the Predicative Calculus of Cumulative Inductive
    Constructions, PCUIC) into a simply-typed functional language
    ({!Miniml}). This step performs type erasure (removing propositions,
    universe levels, implicit arguments) and computes signatures tracking
    which arguments survive extraction ([Keep]/[Kill]).  Its output is read by
    {!Extract_env}, which collects the declarations a run needs and hands them
    to translation.

    For the C++ backend it also records facts later stages cannot recover from
    the ML AST alone: promoted type variables of type classes, higher-kinded
    parameter positions, class-argument shapes of instances, sigma-type
    preconditions, and value-dependent type schemes (all in {!Table}). *)

open Names
open Declarations
open Environ
open Evd
open Miniml

(** Extract a single constant definition into an ML declaration: a [Dtype]
    for a type scheme, a [Dterm] for anything else (an axiom's body is
    [MLaxiom], a logical constant's [MLdummy]).  A definition also records its
    instance class shape and context instance applications in {!Table}.
    @param access Indirect accessor used to force opaque proof bodies when [access_opaque ()] is set
    @param env Rocq global environment
    @param kn The constant name to extract
    @param cb The constant body (declaration) from the environment *)
val extract_constant :
  Global.indirect_accessor -> env -> Constant.t -> constant_body -> ml_decl

(** Extract the type signature of a constant (for module signatures).
    @param env Rocq global environment
    @param kn The constant name whose spec is extracted
    @param cb The constant body.  A type scheme's [Def] body becomes the
    [Stype]'s abbreviation; a term's [Def] body is extracted as the [Sval]'s
    value.  A type scheme taking a value argument whose body does not extract
    is recorded with {!Table.add_value_dep_type_scheme}. *)
val extract_constant_spec :
  env -> Constant.t -> ('a, 'b) pconstant_body -> ml_spec

(** Extract a [module ... with Definition ... := ...] constraint.
    @param env Rocq global environment
    @param sg Evar map for universe and constraint tracking
    @param c The constrained term (right-hand side of the [with] clause)
    @return [Some (vars, ty)] if [c] is an informative type scheme, [None] if logical *)
val extract_with_type :
  env -> evar_map -> EConstr.t -> (Id.t list * ml_type) option

(** Extract a mutual fixpoint definition into one [Dfix], each member's body
    with the group's recursive [Rel]s replaced by its constants.  A cofixpoint
    group's members are registered with {!Table.add_cofixpoint}.
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

(** Extract a (mutual) inductive type definition.  The result's constructor
    argument lists omit erased and implicit arguments; the cached
    {!Table.lookup_ind} entry keeps them. *)
val extract_inductive : env -> MutInd.t -> ml_ind

(** Extract a single term, for [Crane Show Extraction] on the current proof.
    A type scheme extracts to [MLdummy Ktype], a logical term to
    [MLdummy Kprop].
    @param env Rocq global environment
    @param sg Evar map for universe and constraint tracking
    @param c The term to extract
    @return A pair [(ast, ty)] of the extracted ML expression and its ML type *)
val extract_constr : env -> evar_map -> EConstr.t -> ml_ast * ml_type

(** Is the declaration purely logical (erased during extraction)? *)
val logical_decl : ml_decl -> bool

(** Is the specification purely logical? *)
val logical_spec : ml_spec -> bool
