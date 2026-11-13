(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A copy of a Core term that is new terms: the same shape, with every
    occurrence fresh.  Used where a pass duplicates a body, such as inlining
    a callee at a call.

    Every consumer of Core names a place in a definition by an occurrence: a
    read's, a let's, a match's, a construction's, a coercion's, a local fixpoint's or a global use's -- the recursion
    plan's calls, ControlIR's turns, the ownership plan's reads and the C++
    call made of a Core call all do.  A copy keeping the original's would be
    two places with one name, so a copy mints every occurrence afresh.  It
    also renames apart what its annotations leave open, open annotations and
    holes, which a reader of the copy may fill and a reader of the original
    must not see filled.  Binders need nothing: a {!Core_binder.t} is
    positional in the definition the copy lands in. *)

(** [copy e]: [e], every occurrence in it fresh and its open annotations
    and holes renamed apart from [e]'s. *)
val copy : Miniml.ml_ast -> Miniml.ml_ast

(** [instance use body]: [body], the definition of [use]'s callee, copied
    ({!copy}) at the use: each variable of the callee's scheme the use
    solves is replaced by its solution, in the annotations and in the
    instantiations of the uses inside the body -- a rigid self-reference
    there ({!Scheme.Identity}) included, whose variable is the callee's.
    Substitution reaches every variable of the callee's range, as
    {!Mlutil.instantiate_body}'s does: a local definition's own variable
    numbered within it ({!Local_types}) is replaced too. *)
val instance : Miniml.global_use -> Miniml.ml_ast -> Miniml.ml_ast

(** [call ~ty use body args]: the call of [use]'s callee, defined as [body]
    at type [ty], to [args], as the callee's body ({!instance}) with each
    parameter given its argument: a variable or an erased value is read
    where the parameter is, any other argument bound to the parameter by a
    let, outermost first, at the type translation generates the parameter
    at.  [None] unless [args] is exactly one argument per parameter the type
    declares, each bound by a lambda of [body].  [args] stand where the call
    does, and are moved there, not copied. *)
val call : ty:Miniml.ml_type -> Miniml.global_use -> Miniml.ml_ast -> Miniml.ml_ast list -> Miniml.ml_ast option
