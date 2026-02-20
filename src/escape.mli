(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*s Smart pointer optimization for MiniML AST.

    Three-phase optimization strategy:

    Phase 1 (unique_ptr):
      Promote local shared_ptr to unique_ptr when safe (single use, no escape).

    Phase 2 (owned/borrowed):
      Infer whether function parameters need ownership (pass by value)
      or can borrow (pass by const reference).

    Phase 3 (reset/reuse):
      Reuse memory cells in pattern matches when use_count() == 1. *)

open Miniml

(* ========================================================================== *)
(*  Phase 1: unique_ptr optimization                                         *)
(* ========================================================================== *)

(** [analyze body] returns MLletin depth indices (0-based) whose bindings
    are safe to convert from shared_ptr to unique_ptr.
    Safe when: (1) non-enum, non-coinductive inductive type,
               (2) not Dummy,
               (3) occurs ≤ 1 time in continuation (max over branches),
               (4) does not escape. *)
val analyze : ml_ast -> int list

(** [nb_occur_match k t] counts occurrences of de Bruijn index [k] in [t],
    using maximum over branches (safe conservative estimate). *)
val nb_occur_match : int -> ml_ast -> int

(* ========================================================================== *)
(*  Phase 2: owned/borrowed parameter inference                              *)
(* ========================================================================== *)

(** [infer_owned_params n body] returns a bool list of length [n].
    Element [i] is true when the parameter at de Bruijn index [i+1]
    needs ownership (pass by value: shared_ptr<T>), false when it
    can be borrowed (pass by const ref: const shared_ptr<T>&).

    De Bruijn indexing: 1 = innermost/last parameter.
    Output order: element 0 → de Bruijn 1, element 1 → de Bruijn 2, etc. *)
val infer_owned_params : int -> ml_ast -> bool list

(* ========================================================================== *)
(*  Phase 3: reset/reuse optimization                                        *)
(* ========================================================================== *)

(** [find_reuse_candidates scrutinee_type branches] identifies branches
    where the result constructs a value of the same inductive type with
    the same constructor arity as the matched pattern. When the scrutinee
    has use_count() == 1, we can reuse its memory cell instead of allocating.

    Returns: [(branch_idx, matched_ctor, arity, tail_ctor, tail_args)] *)
val find_reuse_candidates :
  ml_type -> ml_branch array ->
  (int * Names.GlobRef.t * int * Names.GlobRef.t * ml_ast list) list

(* ========================================================================== *)
(*  Utility functions                                                        *)
(* ========================================================================== *)

module IntSet : Set.S with type elt = int

(** [free_rels depth t] returns free de Bruijn indices in [t],
    shifted by [depth]. An index [i > depth] contributes [i - depth]. *)
val free_rels : int -> ml_ast -> IntSet.t

(** [is_shared_ptr_type ty] returns true if [ty] is a non-enum,
    non-coinductive inductive (wrapped in shared_ptr in C++). *)
val is_shared_ptr_type : ml_type -> bool
