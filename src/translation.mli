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

open Common
open Miniml
open Minicpp
open Names

(** Raised when a translation feature is not yet implemented. *)
exception TODO

(** {2 Local Inductive Context}
    Tracks inductives defined in the current module scope.
    When set, references to these inductives won't be wrapped in Tnamespace,
    so they appear as sibling types rather than outer-namespace-qualified types. *)

val add_local_inductive : GlobRef.t -> unit
val clear_local_inductives : unit -> unit
val get_local_inductives : unit -> GlobRef.t list

(** {2 Type Conversion}
    Convert Miniml types to Minicpp types. *)

(** Convert an ML type to C++ type representation.
    @param env The current variable environment
    @param ns List of inductive references that should be treated as local (no namespace wrapper)
    @param tvars Type variable names for substitution
    @param ml_type The ML type to convert *)
val convert_ml_type_to_cpp_type : env -> GlobRef.t list -> Id.t list -> ml_type -> cpp_type

(** {2 Expression Generation} *)

(** Generate a C++ expression from an ML AST. *)
val gen_expr : env -> ml_ast -> cpp_expr

(** Generate pattern matching as a C++ expression using std::visit. *)
val gen_cpp_case : ml_type -> ml_ast -> env -> ml_branch array -> cpp_expr

(** {2 Declaration Generation} *)

(** Generate C++ declaration for a term definition.
    Returns (decl, env, type_variables). *)
val gen_decl : GlobRef.t -> ml_ast -> ml_type -> cpp_decl * env * variable list

(** Similar to gen_decl but returns None for non-function types (used by pp_hdecl). *)
val gen_decl_for_pp : GlobRef.t -> ml_ast -> ml_type -> cpp_decl option * env * variable list

(** Generate C++ function specification (declaration without body). *)
val gen_spec : GlobRef.t -> ml_ast -> ml_type -> cpp_decl * env

(** Generate C++ definitions for a group of mutually recursive functions. *)
val gen_dfuns : GlobRef.t array * ml_ast array * ml_type array -> (cpp_decl * env * variable list) list

(** Generate C++ headers (declarations) for a group of mutually recursive functions. *)
val gen_dfuns_header : GlobRef.t array * ml_ast array * ml_type array -> (cpp_decl * env) list

(** {2 Inductive Type Generation} *)

(** Generate C++ code for an inductive type (older style with make functions). *)
val gen_ind_cpp : variable list -> GlobRef.t -> GlobRef.t array -> ml_type list array -> cpp_decl

(** Generate C++ code for a record type. *)
val gen_record_cpp : GlobRef.t -> GlobRef.t option list -> ml_ind_packet -> cpp_decl

(** Generate C++ concept for a type class. *)
val gen_typeclass_cpp : GlobRef.t -> GlobRef.t option list -> ml_ind_packet -> cpp_decl

(** Generate C++ header for an inductive type (older style). *)
val gen_ind_header : variable list -> GlobRef.t -> GlobRef.t array -> ml_type list array -> cpp_decl

(** Generate C++ header for an inductive type (v2 style: encapsulated struct with methods).
    @param vars Template type parameter names
    @param name The inductive type reference
    @param cnames Constructor references
    @param tys Constructor argument types
    @param method_candidates Functions to generate as methods: (func_ref, body, type, this_position) *)
val gen_ind_header_v2 : variable list -> GlobRef.t -> GlobRef.t array -> ml_type list array -> (GlobRef.t * ml_ast * ml_type * int) list -> cpp_decl

(** Generate methods for eponymous records.
    For records merged into module structs, this generates instance methods from functions
    that take the record as first argument.
    @param name The record type reference
    @param vars Template type parameter names
    @param method_candidates Functions to generate as methods: (func_ref, body, type, this_position)
    @return List of method fields with visibility *)
val gen_record_methods : GlobRef.t -> variable list -> (GlobRef.t * ml_ast * ml_type * int) list -> (cpp_field * cpp_visibility) list

(** {2 Type Class Instance Generation} *)

(** Generate a C++ struct for a type class instance.
    Type class instances become structs with static methods.
    Returns (struct_decl option, class_ref option, type_args).
    The class_ref and type_args are used by cpp.ml to generate static_assert
    verifying the instance satisfies the concept. *)
val gen_instance_struct : GlobRef.t -> ml_ast -> ml_type
    -> cpp_decl option * GlobRef.t option * ml_type list

(** Check if a term is a type class instance (constructs a type class record). *)
val is_typeclass_instance : ml_ast -> ml_type -> bool
