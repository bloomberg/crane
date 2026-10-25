(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A recursive function specialized to the lambda a definition passes it,
    and the specialized body simplified where its arguments are known.

    A definition whose whole body is a call [f .. (fun x => b) ..] to a
    recursive function that passes that parameter unchanged to every
    recursive call becomes a copy of [f] with the lambda in place of the
    parameter: [interp h := iter (fun t => match observe t with ..)] becomes
    a fixpoint of its own -- only where the copy can be the definition's own
    fixpoint, its other arguments being the definition's parameters, since a
    fixpoint left local is not suspended the way a corecursive one must be.
    The copy is then simplified with two rewrites, neither of which knows
    any particular function:

    - a call to a global with a known constructor among its arguments -- a
      constructor, or a definition that is one, like [Ret x] -- is unfolded,
      and kept only if what it reduces to is smaller: [bind (Ret x) k]
      unfolds through [bind], [subst] and [observe] to [k x];
    - a call with a match among its arguments, the others being values, is
      pushed into the match's branches, and kept only if some branch then
      unfolds.

    Unfolding a corecursive function evaluates, where its argument is
    already a value, what its cofixpoint would have evaluated when first
    observed, so the tree is the same tree, node for node.  The copy is a
    fixpoint of the definition itself, which Crane suspends as it does any
    other.  A definition no rewrite shrinks is left exactly as it was. *)

val structure : Miniml.ml_structure -> Miniml.ml_structure

(** A definition of the structure: a term and its type, or a fixpoint of
    one function. *)
type def =
  | Term of Miniml.ml_ast * Miniml.ml_type
  | Fix of Miniml.ml_fix_def

(** The structure's definitions, those inside its modules included. *)
val definitions : Miniml.ml_structure -> def Ref.User.Map.t

(** The body of the global a use names, where it may be unfolded, at the
    type arguments the use wrote: [None] for a mapped global, and where the
    use did not write an argument for every variable its type mentions. *)
val body_of : def Ref.User.Map.t -> Miniml.global_use -> Miniml.ml_ast option

(** [instantiate b args]: [b] applied to [args], its leading lambdas
    instantiated: a value argument substituted, any other bound once by a
    [let] where its parameter is read more than once.  Arguments past [b]'s
    lambdas stay applied; [None] where there are fewer arguments than
    lambdas. *)
val instantiate : Miniml.ml_ast -> Miniml.ml_ast list -> Miniml.ml_ast option
