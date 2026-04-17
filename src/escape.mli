(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Smart pointer optimization for MiniML AST.

    Two-phase optimization strategy:

    Phase 1 (owned/borrowed): Infer whether function parameters need ownership
    (pass by value) or can borrow (pass by const reference).

    Phase 2 (reset/reuse): Reuse memory cells in pattern matches when
    use_count() == 1. *)

open Miniml

(** [nb_occur_match k t] counts occurrences of de Bruijn index [k] in [t], using
    maximum over branches (safe conservative estimate). *)
val nb_occur_match : int -> ml_ast -> int

(** [escapes k t] checks if de Bruijn index [k] escapes in [t] (value outlives
    its scope). Escaping positions: constructor args, lambda captures, tail
    position, fixpoint captures, partial-application captures. *)
val escapes : int -> ml_ast -> bool

(** [partial_app_remaining head args] returns [Some remaining] when
    [MLapp(head, args)] is a partial application with [remaining] args still
    needed.  Returns [None] when fully applied.  Only handles [MLglob]
    heads. *)
val partial_app_remaining : ml_ast -> ml_ast list -> int option

(** [is_partial_app head args] returns [true] when [MLapp(head, args)] is a
    partial application — i.e., fewer non-dummy arguments than the function's
    value-level arity. Only handles [MLglob] heads. *)
val is_partial_app : ml_ast -> ml_ast list -> bool

(** [single_use_nargs k t] finds the single use of [MLrel k] in [t] and
    returns how many non-dummy args it is applied to (0 if bare).

    @precondition [k] must occur at most once in [t]. If [k] occurs
    multiple times, returns the arg count of the {i last} occurrence found.
    Verify with [nb_occur_match k t <= 1] before calling. *)
val single_use_nargs : int -> ml_ast -> int

(** {2 Phase 1: owned/borrowed parameter inference} *)

(** [infer_owned_params n body] returns a bool list of length [n]. Element [i]
    is true when the parameter at de Bruijn index [i+1] needs ownership (pass by
    value: shared_ptr<T>), false when it can be borrowed (pass by const ref:
    const shared_ptr<T>&).

    De Bruijn indexing: 1 = innermost/last parameter. Output order: element 0 →
    de Bruijn 1, element 1 → de Bruijn 2, etc. *)
val infer_owned_params : int -> ml_ast -> bool list

(** {2 Phase 2: reset/reuse optimization} *)

(** [find_reuse_candidates scrutinee_type branches] identifies branches where
    the result constructs a value of the same inductive type with the same
    constructor arity as the matched pattern. When the scrutinee has use_count()
    == 1, we can reuse its memory cell instead of allocating.

    Returns: [(pv_idx, variant_idx, matched_ctor, arity, tail_ctor, tail_args)]
    where [pv_idx] is the position in the pattern vector (for array access) and
    [variant_idx] is the constructor's 0-based index in the C++ variant (for the
    [use_count()==1 && v().index()==N] runtime check). *)
val find_reuse_candidates :
  ml_type ->
  ml_branch array ->
  (int * int * Names.GlobRef.t * int * Names.GlobRef.t * ml_ast list) list

(** {2 Utility functions} *)

(** Set of integers for tracking de Bruijn indices. *)
module IntSet : Set.S with type elt = int

(** [free_rels depth t] returns free de Bruijn indices in [t], shifted by
    [depth]. An index [i > depth] contributes [i - depth]. *)
val free_rels : int -> ml_ast -> IntSet.t

(** [is_shared_ptr_type ty] returns true if [ty] is a non-enum, non-coinductive
    inductive (wrapped in shared_ptr in C++). *)
val is_shared_ptr_type : ml_type -> bool
