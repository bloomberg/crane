(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** ControlIR (docs/Pipeline-Disentangling-Plan.md, sections 4.9 and 6.4):
    a function's control as it is implemented, before any C++ is chosen for
    it.  The terms it does not change stay Core ({!Miniml.ml_ast}); what it
    makes explicit is where control goes.

    It holds the loops of direct tail recursion: a function that recurses
    only by tail calls is a [Loop] over its parameters, each of its
    recursive calls a [Continue] of it, and every other way out a [Return].
    And those of tail modulo cons: a recursive call held in a chain of
    constructors returned is a [Continue_into], whose constructors are made
    around a hole the next turn fills.  And those of a machine with a
    stack: a recursive call whose result a let or a sequential bind binds
    is a [Resume], where the machine resumes once the call has returned.
    {!Lower_control} produces them. *)

(** What a loop is the loop of: a function of the program, or the member
    [m] of the local fixpoint [occurrence]. *)
module Loop : sig
  type t =
    | Function of Names.GlobRef.t
    | Member of Miniml.Occurrence.t * int

  val equal : t -> t -> bool
end

module Term : sig
  type t =
    | Loop of loop
    | Let of let_
    | Match of match_
    | Return of Miniml.ml_ast
    | Continue of continue_
    | Continue_into of continue_into
    | Resume of resume

  (** The loop [loop] over [parameters], outermost first, running [body]. *)
  and loop = {
    loop : Loop.t;
    parameters : (Miniml.ml_ident * Miniml.ml_type) list;
    body : t;
  }

  (** [value] bound to [binder] while [body] runs: a let, or a sequential
      bind's action and its continuation's parameter. *)
  and let_ = {
    binder : Miniml.ml_ident;
    binder_type : Miniml.ml_type;
    value : Miniml.ml_ast;
    body : t;
  }

  and match_ = {
    scrutinee_type : Miniml.ml_type;
    scrutinee : Miniml.ml_ast;
    branches : branch list;
  }

  and branch = {
    binders : (Miniml.ml_ident * Miniml.ml_type) list;
    result_type : Miniml.ml_type;
    pattern : Miniml.ml_pattern;
    body : t;
  }

  (** The next turn of [target], its parameters taking [arguments]: the
      recursive call made of [occurrence], the use of the global or the read
      of the member heading it. *)
  and continue_ = {
    target : Loop.t;
    occurrence : Miniml.Occurrence.t;
    arguments : Miniml.ml_ast list;
  }

  (** The next turn of a loop building what this one returns, tail modulo
      cons: the constructors [cells], outermost first, each held in the hole
      of the one around it, are made with the innermost's hole left empty,
      and [next] continues the loop to fill it. *)
  and continue_into = {
    cells : cell list;
    next : continue_;
  }

  (** The constructor [constructor] applied to [arguments], in its declared
      order, with its argument [hole] left out: the hole. *)
  and cell = {
    constructor : Names.GlobRef.t;
    hole : int;
    arguments : Miniml.ml_ast list;
  }

  (** [value] run for the value [binder] takes while [body] runs, where
      [value] makes recursive calls: each [Continue] in it enters the loop
      afresh, and [body] resumes once that turn returns, its result bound to
      [binder]; each [Return] in it is the value bound so. *)
  and resume = {
    binder : Miniml.ml_ident;
    binder_type : Miniml.ml_type;
    value : t;
    body : t;
  }
end

(** The occurrences of the calls [t] continues a loop by, in order, those
    resumed after included. *)
val continues : Term.t -> Miniml.Occurrence.t list

(** The occurrences of the calls [t] enters its loop by afresh and resumes
    after, in order: the [Continue]s in the value of a [Resume]. *)
val resumed : Term.t -> Miniml.Occurrence.t list

(** The turns of [t] that build what they return, tail modulo cons, in
    order. *)
val continues_into : Term.t -> Term.continue_into list

(** [t] with [f] applied to the value of every [Return] in it. *)
val map_returns : (Miniml.ml_ast -> Miniml.ml_ast) -> Term.t -> Term.t

(** For each parameter of the loop [l], outermost first, whether every
    [Continue] of [l] passes it on unchanged: its argument there is a read of
    that parameter.  Such a parameter keeps its value for as long as the loop
    runs. *)
val invariant_parameters : Term.loop -> bool list
