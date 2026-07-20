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
open Table

(** {2 Local Inductive Context}
    Tracks inductives defined in the current module scope. When set, references
    to these inductives won't be wrapped in Tnamespace, so they appear as
    sibling types rather than outer-namespace-qualified types. *)

(** Record an inductive as defined in the current module scope. *)
val add_local_inductive : GlobRef.t -> unit

(** Reset the local-inductive set. Called at module boundaries. *)
val clear_local_inductives : unit -> unit

(** Return the inductives currently recorded as local to this module scope. *)
val get_local_inductives : unit -> GlobRef.t list

(** Set method_self_ns from local_inductives for standalone functions.
    Returns the saved previous value for restoration via
    {!restore_method_self_ns}. *)
val set_method_ns_for_locals : unit -> Refset'.t

(** Restore method_self_ns to a previously saved value. *)
val restore_method_self_ns : Refset'.t -> unit

(** Return the codomain of an ML type, chasing through arrows and meta
    indirections. For [A -> B -> C] this returns [C]. *)
val ml_codomain : Miniml.ml_type -> Miniml.ml_type

(** {2 Type Conversion}
    Convert Miniml types to Minicpp types. *)

(** Convert an ML type to C++ type representation.
    @param env The current variable environment
    @param ns
      Set of inductive references that should be treated as local (no namespace
      wrapper). Defaults to empty; most callers omit it.
    @param tvars Type variable names for substitution
    @param ml_type The ML type to convert *)
val convert_ml_type_to_cpp_type :
  env -> ?ns:Refset'.t -> Id.t list -> ml_type -> cpp_type

(** Check if a C++ type is erased to std::any (for indexed inductive methods).
    Returns true if the type is Tany or contains an unnamed Tvar. *)
val type_is_erased : cpp_type -> bool

(** {2 Expression Generation} *)

(** Generate a C++ expression from an ML AST. *)
val gen_expr : ?expected_ty:cpp_type -> env -> ml_ast -> cpp_expr

(** Generate pattern matching as a C++ expression using std::visit. *)
val gen_cpp_case : ml_type -> ml_ast -> env -> ml_branch array -> cpp_expr

(** Generate C++ statements from an ML AST. The continuation [k] transforms the
    final expression into a statement (e.g., return, assignment). Handles
    let-bindings, pattern matching, fix expressions, and monadic operations. *)
val gen_stmts : env -> (cpp_expr -> cpp_stmt) -> ml_ast -> cpp_stmt list

(** Try eta-expanding/applying [f] to [args] when a call is under-applied or
    involves a type-erased higher-order callback. Falls back to a plain
    application. *)
val eta_fun : env -> ml_ast -> ml_ast list -> cpp_expr

(** Strip [MLmagic] wrappers recursively — [MLmagic] is a transparent coercion
    in the ML AST and should be ignored by numeral-folding traversals. *)
val strip_magic : ml_ast -> ml_ast

(** {2 Declaration-Generation Helper Functions}
    Pure helpers shared between the expression-level codegen above and the
    declaration-level generators in {!Gen_decls}. *)

(** Return a prefix of [lst] with length [min(n, length lst)], never raising
    when [n > length lst]. *)
val safe_firstn : int -> 'a list -> 'a list

(** Extract the innermost result type from a (possibly monadic) ML type. *)
val ml_result_type : ml_type -> ml_type

(** Check if a monad reference uses the reified ITree extraction mode. *)
val is_monad_reified : GlobRef.t -> bool

(** If the codomain of [ty] is a registered monad, return its reference. *)
val extract_monad_from_codomain : ml_type -> GlobRef.t option

(** Collect [Id.t]s for typeclass-typed parameters in an ML arrow type. *)
val collect_typeclass_param_ids : ml_type -> Id.t list

(** Apply unit-to-void conversion on a C++ type, respecting reified mode. *)
val apply_unit_void : bool -> bool -> cpp_type -> cpp_type

(** Generate the C++ expression for Rocq's [tt] (the unit constructor). *)
val mk_tt_expr : unit -> cpp_expr

(** Qualify inductive type references with {!Minicpp.Tnamespace}, subject to
    a [skip] predicate that leaves selected inductives unwrapped. *)
val qualify_inductives : ?skip:(GlobRef.t -> bool) -> cpp_type -> cpp_type

(** Render a C++ type as a string suitable for use in raw C++ template
    arguments, applying post-hoc name fixups. *)
val render_cpp_type_for_raw_template :
  ?raw_inductives:Refset'.t -> ?no_custom_inductives:Refset'.t ->
  cpp_type -> string

(** Build guard-compare statements for a constructor whose fields alias-check
    two identical-typed pointer parameters. *)
val build_guard_compare_stmts :
  GlobRef.t -> (Id.t * cpp_type) list -> cpp_stmt list

(** Post-processing pass: insert [std::move] for the state-threading pattern
    in tail-recursive functions returning [pair<S,R>]. *)
val rewrite_state_threading_moves :
  GlobRef.t -> Id.t -> cpp_type -> (Id.t * cpp_type) list -> cpp_stmt list ->
  (Id.t * cpp_type) list * cpp_stmt list

(** Generate a C++ expression converting [expr] from [src_ty] to [dst_ty],
    inserting [make_shared]/dereference/etc. as needed. *)
val gen_type_conversion_expr :
  ?skip:(GlobRef.t -> bool) -> src_ty:cpp_type -> dst_ty:cpp_type ->
  cpp_expr -> cpp_expr

(** Reify a parameter's ML type into its monadic-aware C++ form (e.g.
    voidifying [Unit] results inside [ITree] callbacks). *)
val reify_monadic_param_type : ml_type -> cpp_type -> cpp_type

(** Collect [Tvar] indices referenced by an ML type, added to the accumulator
    list. *)
val collect_tvars : int list -> ml_type -> int list

(** True when evaluating an ML AST may throw through an extracted axiom or
    exception. *)
val ast_may_throw : ml_ast -> bool

(** Detect which of the first [n_params] parameters (by de Bruijn index) are
    NOT simply forwarded unchanged to a self/recursive call, per
    [is_self_call]. *)
val detect_non_forwarded_params_generic :
  is_self_call:(int -> ml_ast -> bool) -> int -> ml_ast -> int list

(** Infer, for each of [n_params] parameters, whether it is "owned" (should be
    passed by value / moved) based on escape analysis of [body]. *)
val infer_owned_flags :
  int -> ml_ast -> ('a * ml_type) list -> bool list

(** Wrap a C++ parameter type with const/ref based on ownership semantics. *)
val wrap_param_by_ownership : ?is_owned:bool -> cpp_type -> cpp_type

(** True when a single-branch match body is a direct projection returning a
    field stored as an erased [std::any]. *)
val ml_body_returns_erased_field : ml_ast -> bool

(** True when the head of an application chain is (or was) wrapped in
    [MLmagic]. *)
val ml_head_has_magic : ml_ast -> bool

(** Build a [Tvar i -> concrete_type] substitution mapping for extra type
    variables introduced beyond an inductive's own [num_ind_vars]. *)
val make_subst_extra_tvars :
  int -> (int * Id.t) list -> cpp_type -> cpp_type

(** Rewrite lambda bodies so their statement lists are treated as
    capture-by-value contexts (used when hoisting closures). *)
val return_captures_by_value : cpp_stmt list -> cpp_stmt list

(** Unify the (possibly polymorphic) declared type [ty] against the concrete
    types occurring in body [b], substituting resolved type variables so
    [gen_decl] can print a monomorphic signature even for polymorphic
    definitions. *)
val resolve_body_tvars : ml_ast -> ml_type -> ml_ast

(** Compute the factory method name for a constructor (see
    {!Translation.factory_name_of_ctor} implementation notes). *)
val factory_name_of_ctor : ?type_name:string -> string -> string

(** Augment [kernel_arg_names] with names from an [Arguments] declaration.
    Where [kernel_arg_names] has [None] (anonymous binder), the corresponding
    entry from [Arguments_renaming.arguments_names] is used if present and
    non-anonymous.  Kernel-named entries ([Some _]) are never overridden.
    Returns [kernel_arg_names] unchanged if [Arguments_renaming] has no entry
    for [cref] or if all kernel binders are already named. *)
val augment_with_args_renaming :
  GlobRef.t -> Id.t option list -> Id.t option list

(** Compute and register field names for all [n_fields] fields of a
    constructor struct.  [field_consarg_names] supplies the pretty names used
    for struct field declarations (may include [Arguments_renaming] overrides);
    [bind_consarg_names] supplies the kernel-only names used for structured-
    binding variable generation. *)
val compute_and_register_field_names :
  string -> Id.t option list -> Id.t option list -> int -> Id.t list


(** Clear and return any pending lifted declarations. Used to prevent stale
    lifted decls from leaking between extraction passes. *)
val take_lifted_decls : unit -> cpp_decl list

(** Reset the seen-lifted-refs deduplication set. Call at the start of each
    new output file so that identical helpers in different files are NOT
    suppressed. *)
val clear_seen_lifted_refs : unit -> unit


(** [is_list_global g] returns true iff [g] is the Coq list inductive.
    Exposed so that cpp_print.ml can detect list types in any_cast contexts. *)
val is_list_global : GlobRef.t -> bool

(** [has_tvar ty] returns true iff [ty] contains any type variable
    ([Tvar], [Tvar'], [Tunknown], or unresolved [Tmeta]). *)
val has_tvar : Miniml.ml_type -> bool
