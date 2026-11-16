(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Canonical application spines: each call read whole, written into the
    program once so that no later pass rediscovers it.  In a canonical term
    no application's head is

    - a global already applied: [(f a) b] is [f a b];
    - a coercion: [(magic f) a] is [f a];
    - a match with one branch, which is a destructuring and nothing else:
      [(let (x, y) := p in g x) a] is [let (x, y) := p in g x a];
    - an erased value or a throw, the eliminator of a branch the indices
      rule out: applied, it is itself, never evaluating its arguments;

    and no term is a numeral converter applied to a digit chain, or a
    constructor term of a numeral inductive spelling a number: each is the
    literal it computes ({!Numeral_literal.fold}).

    The contract is total.  {!structure} makes every definition body
    canonical before {!Normalize.structure} reads it, which keeps it so --
    it names calls by variables, and a partner it splices in stands for its
    parameters by variables or lets ({!check}) -- extraction makes the terms
    a type carries canonical where it builds them
    ([Rocq_to_core.Extraction.extract_type_app]), and every application built later is
    built with {!apply} or {!Base.Core_util.apply_eta_args}.  So translation
    reads each call as it is written, and an analysis of the structure --
    which parameters a call owns ({!Escape}) -- reads the same call the
    printer emits: a global applied in stages had its first stage taken for
    a partial application that captures its arguments. *)

(** [apply f args], [f] and [args] canonical: the canonical form of
    [Core.Expr.Apply (f, args)] ({!Base.Core_util.canonical_app}), a literal where it is a
    numeral converter's application to a digit chain.  Every application
    built after {!structure} has run is built with this. *)
val apply : 'p Core.Expr.at -> 'p Core.Expr.at list -> 'p Core.Expr.at

(** [spine e] is [e] with every application canonical and every numeral
    literal written as one. *)
val spine : 'p Core.Expr.at -> 'p Core.Expr.at

(** Whether [f] may stand at the head of an application of a canonical
    term. *)
val canonical_head : 'p Core.Expr.at -> bool

(** Whether the node [e] is canonical: not an application with a head
    {!canonical_head} rejects, nor a term {!spine} writes as a literal. *)
val canonical_application : 'p Core.Expr.at -> bool

(** Whether every application in a term is canonical. *)
val is_canonical : 'p Core.Expr.at -> bool

(** [check s]: under [CRANE_CHECK_IR], a violation for each definition of
    [s] whose body is not canonical. *)
val check : 'p Core.Program.at -> unit

(** [structure s]: {!spine} on the body of every definition of [s]. *)
val structure : 'p Core.Program.at -> 'p Core.Program.at
