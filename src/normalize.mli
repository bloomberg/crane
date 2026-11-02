(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Normalized bodies: in a function that will be loopified, every call to
    its own recursive group that sits at a strictly evaluated, non-tail
    position is bound to a variable before the expression that uses it, in
    evaluation order.  The loop transform then meets recursive calls only as
    [auto r = f(...);] statements, a tail [return f(...)], or the last
    recursive argument of a constructor that builds a cell -- what tail modulo
    cons rewrites.

    MiniML is pure and strict, so binding an argument before its application
    preserves meaning; nothing is taken out of a branch, a lambda body or a
    let body, which may not run.  What follows a match bound to a variable
    is copied into its branches instead ({!into_branches}), so the calls
    ending them are turns too. *)

(** [eta_expand s] gives every definition in [s] a parameter at each arrow
    of its type, applying the body it writes to the ones it leaves out: the
    body translation generates, here once for every consumer instead of
    re-derived by each.  It runs first in {!Core.normalize}, so the calls
    {!structure} names are those of that body. *)
val eta_expand : Miniml.ml_structure -> Miniml.ml_structure

(** [let_lambdas s] puts every let-bound lambda in [s]'s definitions as it is
    generated ({!Core_elaborate.generated_definition}): an alias of a
    polymorphic function inlined, one used at a single instance bound at it,
    one bound as a value eta-expanded.  It runs after {!eta_expand} and
    before {!structure}, which then names the calls an inlined alias
    makes. *)
val let_lambdas : Miniml.ml_structure -> Miniml.ml_structure

(** [into_branches ~fresh ~rty (id, ty, occ) branches rest]: the branches
    of [let id : ty := match _ with branches in rest] ([occ] the let's) with
    what follows the match copied into each, after the branch's own lets:
    [p => let id : ty := b in rest], each branch now of type [rty], the type
    of [rest].  The first branch keeps [rest], [id] and [occ]; every other
    gets a copy of [rest] with fresh occurrences ({!Core_copy.copy}), its
    temporaries, [id] if one, renamed by [fresh], and a let occurrence of its
    own.  [None] where the copies would add more than a fixed budget of
    nodes. *)
val into_branches :
  fresh:(unit -> Miniml.ml_ident) ->
  rty:Miniml.ml_type ->
  Miniml.ml_ident * Miniml.ml_type * Miniml.Occurrence.t ->
  Miniml.ml_branch array ->
  Miniml.ml_ast ->
  Miniml.ml_branch array option

(** [structure p] normalizes every loopified fixpoint group in [p], a
    frozen program ({!Core.normalize}), once each partner a loopified
    function is to have inlined is spliced into it
    ({!Recursion_plan.splice_partners}), and records what splicing
    decided. *)
val structure : Core.normalizing -> Core.normalizing
