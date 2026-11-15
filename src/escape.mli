(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Escape analysis over Core terms, feeding parameter ownership and cell
    reuse.  It runs before translation to CppIR; {!Ownership} settles its
    per-parameter answers for the whole program, and translation reads them.

    Two-phase optimization strategy:

    Phase 1 (owned/borrowed): Infer whether function parameters need ownership
    (pass by value) or can borrow (pass by const reference).

    Phase 2 (reset/reuse): Reuse memory cells in pattern matches when
    use_count() == 1, or unconditionally for a shared variant's block. *)


(** [nb_occur_match k t] counts occurrences of de Bruijn index [k] in [t], using
    maximum over branches (safe conservative estimate).  An argument of an
    inline custom counts once per time its template splices it.

    @param k de Bruijn index to count (1 = innermost binder)
    @param t the Core term to search
    @return number of occurrences; for [Core.Expr.Match] branches the maximum over all
            branches is used (conservative upper bound) *)
val nb_occur_match : int -> Core.Expr.t -> int

(** What an escape query is about, which decides how precisely it reads two
    positions.
    - [Conservative]: a lambda passed as an argument forces its captures to
      escape, and so does a constructor argument.
    - [Of_sub_binding]: a lambda passed as an argument is inspected instead;
      a constructor argument still escapes, so a scrutinee whose
      sub-bindings are rebuilt into a new constructor stays owned and they
      can move out of it.
    - [Of_param]: as [Of_sub_binding], and a constructor argument is read once
      to copy into the new value's field, like a call argument, rather than
      forcing ownership.  Only for a parameter's own ownership, never for
      something extracted from it. *)
type escape_query = Conservative | Of_sub_binding | Of_param

(** [escapes k t] checks if de Bruijn index [k] escapes in [t] (value outlives
    its scope). Escaping positions: constructor args (except for an
    [Of_param] query), lambda captures, tail position, fixpoint captures,
    partial-application captures, and, for an [Of_param] query, an argument
    the callee owns: [callee_flags g] is the ownership of the global [g]'s
    parameters, innermost first, [None] for one nothing settled (the
    default, for every global).

    @param query defaults to [Conservative]
    @param return_escapes whether being returned counts (default [true])
    @param k de Bruijn index to check (1 = innermost binder)
    @param t the Core term to analyse
    @return [true] if the value bound at index [k] may outlive its scope *)
val escapes :
  ?query:escape_query ->
  ?callee_flags:(Names.GlobRef.t -> bool list option) ->
  ?return_escapes:bool ->
  int ->
  Core.Expr.t ->
  bool

(** [partial_app_remaining head args] returns [Some remaining] when
    [Core.Expr.Apply(head, args)] is a partial application with [remaining] args still
    needed.  Returns [None] when fully applied.  Only handles [Core.Expr.Global]
    heads.

    @param head the function head of the application (only [Core.Expr.Global] is handled;
                all other constructors yield [None])
    @param args the list of arguments already supplied, including [Core.Expr.Erased_value]
                placeholders for type-level arguments (which are not counted)
    @return [Some n] where [n] is the number of value-level arguments still
            missing, or [None] if the global's type is unknown or the
            application is fully saturated *)
val partial_app_remaining : Core.Expr.t -> Core.Expr.t list -> int option

(** [is_partial_app head args] returns [true] when [Core.Expr.Apply(head, args)] is a
    partial application — i.e., fewer non-dummy arguments than the function's
    value-level arity. Only handles [Core.Expr.Global] heads.

    @param head the function head of the application
    @param args the arguments already supplied (including [Core.Expr.Erased_value] placeholders)
    @return [true] if at least one value-level argument is still missing *)
val is_partial_app : Core.Expr.t -> Core.Expr.t list -> bool

(** [single_use_nargs k t] finds the single use of [Core.Expr.Bound_variable k] in [t] and
    returns how many non-dummy args it is applied to (0 if bare).

    @precondition [k] must occur at most once in [t]. If [k] occurs
    multiple times, returns the arg count of the {i last} occurrence found.
    Verify with [nb_occur_match k t <= 1] before calling.
    @param k de Bruijn index of the variable to locate (1 = innermost binder)
    @param t the Core term to search
    @return number of non-dummy arguments at the single call site, or [0] if
            the variable appears bare (not as the head of an application) *)
val single_use_nargs : int -> Core.Expr.t -> int

(** {2 Phase 1: owned/borrowed parameter inference} *)

(** [infer_owned_params ~callee_flags n body] returns a bool list of length [n]. Element [i]
    is true when the parameter at de Bruijn index [i+1] needs ownership (pass by
    value), false when it can be borrowed (pass by const reference).  A
    parameter that escapes is owned unless it is only matched on and returned
    unchanged; a parameter matched with a reuse candidate arm
    ({!is_reuse_scrutinee}) is owned when reuse is on.  A parameter passed
    directly to an owned parameter of a callee escapes, since the callee
    keeps it: [callee_flags g] is the ownership of the global [g]'s
    parameters, innermost first, settled across calls ({!Ownership}).

    De Bruijn indexing: 1 = innermost/last parameter. Output order: element 0 →
    de Bruijn 1, element 1 → de Bruijn 2, etc.

    @param n number of parameters to analyse (function arity at the value level)
    @param body the lambda body with parameters still represented as de Bruijn
                indices [1..n]
    @return list of length [n] where element [i] is [true] iff parameter
            [i+1] (de Bruijn) must be passed by value *)
val infer_owned_params :
  callee_flags:(Names.GlobRef.t -> bool list option) -> int -> Core.Expr.t -> bool list

(** [infer_sub_bindings_escape_params n body] returns a bool list of length [n]
    where element [i] is [true] when the parameter at de Bruijn index [i+1] is
    used only as a case scrutinee but its extracted sub-bindings escape into
    constructors.  Callers should only OR this into [infer_owned_params] for
    parameters whose ML type maps to a non-trivially-copyable value type (e.g.,
    custom [prod]), NOT for shared_ptr-backed types ([list], cofix, etc.). *)
val infer_sub_bindings_escape_params : int -> Core.Expr.t -> bool list

(** {2 Projections} *)

(** [returns_receiver_field ~this_pos fn] holds when the function [fn] takes
    one argument, the receiver at [this_pos] (0-based, outermost first), and
    returns one field of it as it is: a single-branch constructor match on
    the receiver whose body is a variable the branch binds.  The result is
    then a place inside the receiver, which a method may lend out rather
    than copy ({!Borrow_projection}). *)
val returns_receiver_field : this_pos:int -> Core.Expr.t -> bool

(** {2 Utility functions} *)

(** Set of integers for tracking de Bruijn indices. *)
module IntSet = Mlutil.IntSet

(** [free_rels depth t] returns free de Bruijn indices in [t], shifted by
    [depth]. An index [i > depth] contributes [i - depth].

    @param depth the current binding depth; indices [<= depth] are considered
                 bound and are not included in the result
    @param t the Core term to scan
    @return set of free indices, each shifted so that 1 denotes the variable
            one level above [depth] *)
val free_rels : int -> Core.Expr.t -> IntSet.t

(** [is_shared_ptr_type ty] returns true if [ty] is a non-enum, non-coinductive,
    non-custom inductive.  The name predates value-type inductives: such a
    type is now usually a value type whose recursive fields are shared
    pointers. *)
val is_shared_ptr_type : Core.Type.t -> bool

(** {2 Phase 2: reuse candidate discovery} *)

(** The [Core.Expr.Construct] nodes [body] returns, wherever it returns one: under its
    [let]s and coercions, and in each branch of a match it ends in.  At most
    one of them is reached on any path through [body]. *)
val tail_constructions : Core.Expr.t -> Core.Expr.t list

(** [find_reuse_candidates pv] returns the match branches whose body builds
    an [Core.Expr.Construct] of the same inductive type as the matched constructor, as
    [(branch_idx, matched_ctor, matched_arity, tail_ctor, tail_args)] tuples.
    The constructors say the type; the caller gates reuse on ownership and a
    runtime [use_count()==1] check. *)
val find_reuse_candidates :
  Core.Match.Branch.t array -> (int * Names.GlobRef.t * int * Names.GlobRef.t * Core.Expr.t list) list

(** [is_reuse_scrutinee k body]: whether [body] matches on parameter [k]
    (de Bruijn, 1 = innermost) with at least one reuse candidate arm, on a
    type whose cells can be recycled. *)
val is_reuse_scrutinee : int -> Core.Expr.t -> bool
