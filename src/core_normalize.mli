(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Canonical application spines: the shape {!Mlutil.read_spine} reads a
    call in, written into the program once so that no later pass rediscovers
    it.  In a canonical term no application's head is

    - a global already applied: [(f a) b] is [f a b];
    - a coercion: [(magic f) a] is [f a];
    - a match with one branch, which is a destructuring and nothing else:
      [(let (x, y) := p in g x) a] is [let (x, y) := p in g x a].

    {!structure} makes every definition body canonical, so an analysis of
    the structure -- which parameters a call owns ({!Escape}) -- reads the
    same call the printer emits: a global applied in stages had its first
    stage taken for a partial application that captures its arguments. *)

(** [apply f args], [f] and [args] canonical: the canonical form of
    [MLapp (f, args)] ({!Mlutil.canonical_app}), for an application built
    after {!structure} has run. *)
val apply : Miniml.ml_ast -> Miniml.ml_ast list -> Miniml.ml_ast

(** [spine e] is [e] with every application canonical
    ({!Mlutil.canonical}). *)
val spine : Miniml.ml_ast -> Miniml.ml_ast

(** Whether [f] may stand at the head of an application of a canonical
    term. *)
val canonical_head : Miniml.ml_ast -> bool

(** [structure s]: {!spine} on the body of every definition of [s]. *)
val structure : Miniml.ml_structure -> Miniml.ml_structure
