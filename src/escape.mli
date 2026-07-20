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
    maximum over branches (safe conservative estimate).

    @param k de Bruijn index to count (1 = innermost binder)
    @param t the MiniML term to search
    @return number of occurrences; for [MLcase] branches the maximum over all
            branches is used (conservative upper bound) *)
val nb_occur_match : int -> ml_ast -> int

(** [escapes k t] checks if de Bruijn index [k] escapes in [t] (value outlives
    its scope). Escaping positions: constructor args, lambda captures, tail
    position, fixpoint captures, partial-application captures.

    @param refined when [true], treats function arguments more precisely: a
                   lambda passed as an argument does not automatically force
                   its captures to escape; instead the lambda body is
                   inspected.  Defaults to [false] (conservative).
    @param k de Bruijn index to check (1 = innermost binder)
    @param t the MiniML term to analyse
    @return [true] if the value bound at index [k] may outlive its scope *)
val escapes : ?refined:bool -> int -> ml_ast -> bool

(** [partial_app_remaining head args] returns [Some remaining] when
    [MLapp(head, args)] is a partial application with [remaining] args still
    needed.  Returns [None] when fully applied.  Only handles [MLglob]
    heads.

    @param head the function head of the application (only [MLglob] is handled;
                all other constructors yield [None])
    @param args the list of arguments already supplied, including [MLdummy]
                placeholders for type-level arguments (which are not counted)
    @return [Some n] where [n] is the number of value-level arguments still
            missing, or [None] if the global's type is unknown or the
            application is fully saturated *)
val partial_app_remaining : ml_ast -> ml_ast list -> int option

(** [is_partial_app head args] returns [true] when [MLapp(head, args)] is a
    partial application — i.e., fewer non-dummy arguments than the function's
    value-level arity. Only handles [MLglob] heads.

    @param head the function head of the application
    @param args the arguments already supplied (including [MLdummy] placeholders)
    @return [true] if at least one value-level argument is still missing *)
val is_partial_app : ml_ast -> ml_ast list -> bool

(** [single_use_nargs k t] finds the single use of [MLrel k] in [t] and
    returns how many non-dummy args it is applied to (0 if bare).

    @precondition [k] must occur at most once in [t]. If [k] occurs
    multiple times, returns the arg count of the {i last} occurrence found.
    Verify with [nb_occur_match k t <= 1] before calling.
    @param k de Bruijn index of the variable to locate (1 = innermost binder)
    @param t the MiniML term to search
    @return number of non-dummy arguments at the single call site, or [0] if
            the variable appears bare (not as the head of an application) *)
val single_use_nargs : int -> ml_ast -> int

(** {2 Phase 1: owned/borrowed parameter inference} *)

(** [infer_owned_params n body] returns a bool list of length [n]. Element [i]
    is true when the parameter at de Bruijn index [i+1] needs ownership (pass by
    value: shared_ptr<T>), false when it can be borrowed (pass by const ref:
    const shared_ptr<T>&).

    De Bruijn indexing: 1 = innermost/last parameter. Output order: element 0 →
    de Bruijn 1, element 1 → de Bruijn 2, etc.

    @param n number of parameters to analyse (function arity at the value level)
    @param body the lambda body with parameters still represented as de Bruijn
                indices [1..n]
    @return list of length [n] where element [i] is [true] iff parameter
            [i+1] (de Bruijn) escapes and must be passed by value *)
val infer_owned_params : int -> ml_ast -> bool list

(** [infer_sub_bindings_escape_params n body] returns a bool list of length [n]
    where element [i] is [true] when the parameter at de Bruijn index [i+1] is
    used only as a case scrutinee but its extracted sub-bindings escape into
    constructors.  Callers should only OR this into [infer_owned_params] for
    parameters whose ML type maps to a non-trivially-copyable value type (e.g.,
    custom [prod]), NOT for shared_ptr-backed types ([list], cofix, etc.). *)
val infer_sub_bindings_escape_params : int -> ml_ast -> bool list

(** {2 Utility functions} *)

(** Set of integers for tracking de Bruijn indices. *)
module IntSet : Set.S with type elt = int

(** [free_rels depth t] returns free de Bruijn indices in [t], shifted by
    [depth]. An index [i > depth] contributes [i - depth].

    @param depth the current binding depth; indices [<= depth] are considered
                 bound and are not included in the result
    @param t the MiniML term to scan
    @return set of free indices, each shifted so that 1 denotes the variable
            one level above [depth] *)
val free_rels : int -> ml_ast -> IntSet.t

(** [is_shared_ptr_type ty] returns true if [ty] is a non-enum, non-coinductive
    inductive (wrapped in shared_ptr in C++). *)
val is_shared_ptr_type : ml_type -> bool
