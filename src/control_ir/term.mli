(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** ControlIR: a function's control as it is implemented, before any C++
    is chosen for it.  The terms it does not change stay Core
    ({!Core.Expr.t}); what it makes explicit is where control goes.

    It holds the loops of direct tail recursion: a function that recurses
    only by tail calls is a [Loop] over its parameters, each of its
    recursive calls a [Continue] of it, and every other way out a [Return].
    And those of tail modulo cons: a recursive call held in a chain of
    constructors returned is a [Continue_into], whose constructors are made
    around a hole the next turn fills.  And those of a machine with a
    stack: a recursive call whose result a let or a sequential bind binds
    is a [Resume], where the machine resumes once the call has returned.
    A machine may have more than one way in: a local fixpoint calling back
    into the function -- a partner's copy spliced into its body among them
    ({!Core_plan.Recursion.splice_partners}) -- is an [Entry] of the function's
    machine rather than a machine of its own, for two machines cannot unwind
    each other's stack.  {!Core_to_control.Lower_control} produces them from a recursive
    Core body, and {!Control_to_cpp.Lower} lowers them to CppIR. *)

(** A function's control. *)
type t =
  | Loop of loop
  | Let of let_
  | Match of match_
  | Return of Core.Expr.t  (** Leaves the function with the Core value. *)
  | Continue of continue_
  | Continue_into of continue_into
  | Resume of resume
  | Entry of entry

(** The loop [loop] over [parameters], outermost first, running [body]. *)
and loop = {
  loop : Loop.t;
  parameters : (Core.Binder_name.t * Core.Type.t) list;
  body : t;
}

(** [value] bound to [binder] while [body] runs: a let, or a sequential
    bind's action and its continuation's parameter. *)
and let_ = {
  binder : Core.Binder_name.t;
  binder_type : Core.Type.t;
  value : Core.Expr.t;
  body : t;
}

(** A match whose branches carry control: the [Core.Expr.Match] it stands
    for, with each branch's body in ControlIR. *)
and match_ = {
  scrutinee_type : Core.Type.t;
  scrutinee : Core.Expr.t;
  branches : branch list;
}

(** One branch of a {!match_}, as Core's {!Core.Match.Branch.t}: the
    pattern's binders, the branch's result type, the pattern, and [body]
    under those binders. *)
and branch = {
  binders : (Core.Binder_name.t * Core.Type.t) list;
  result_type : Core.Type.t;
  pattern : Core.Pattern.t;
  body : t;
}

(** The next turn of [target], its parameters taking [arguments]: the
    recursive call made of [occurrence], the use of the global or the read
    of the member heading it. *)
and continue_ = {
  target : Loop.t;
  occurrence : Core.Occurrence.t;
  arguments : Core.Expr.t list;
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
  arguments : Core.Expr.t list;
}

(** [value] run for the value [binder] takes while [body] runs, where
    [value] makes recursive calls: each [Continue] in it enters the loop
    afresh, and [body] resumes once that turn returns, its result bound to
    [binder]; each [Return] in it is the value bound so. *)
and resume = {
  binder : Core.Binder_name.t;
  binder_type : Core.Type.t;
  value : t;
  body : t;
}

(** A further way into the machine of the loop it stands in, while
    [scope] runs: the loop [entered], a [Continue] of which enters the
    machine there as one of the enclosing loop does.  It is the function
    of a local fixpoint of one member ({!Loop.Member}), its body under
    the fixpoint's name and its parameters, [name] the binder [scope]
    reads it by where a let binds it.  Its [Continue]s of the enclosing
    loop re-enter that loop. *)
and entry = {
  entered : loop;
  name : (Core.Binder_name.t * Core.Type.t) option;
  scope : t;
}

(** The occurrences of the calls [t] continues a loop by, in order, those
    resumed after and those of its entries' loops included. *)
val continues : t -> Core.Occurrence.t list

(** {!continues} of the loop [l] alone: those continuing it rather than
    the loop of one of [t]'s entries. *)
val continues_of : Loop.t -> t -> Core.Occurrence.t list

(** The occurrences of the calls [t] enters its loop by afresh and resumes
    after, in order: the [Continue]s in the value of a [Resume]. *)
val resumed : t -> Core.Occurrence.t list

(** The turns of [t] that build what they return, tail modulo cons, in
    order. *)
val continues_into : t -> continue_into list

(** The loops the entries in [t] enter, in order. *)
val entries : t -> loop list

(** [t] with [f] applied to the value of every [Return] in it. *)
val map_returns : (Core.Expr.t -> Core.Expr.t) -> t -> t

(** For each parameter of the loop [l], outermost first, whether every
    [Continue] of [l] passes it on unchanged: its argument there is a read of
    that parameter.  Such a parameter keeps its value for as long as the loop
    runs. *)
val invariant_parameters : loop -> bool list

(** For each parameter of the loop [l], outermost first, whether every
    [Continue] of [l] passes it a value stored in what the caller passed
    for it, which outlives every turn of the loop: the parameter itself, or
    a binder a pattern binds at a field its constructor stores behind the
    pointer ([pointer_fields] gives those of each constructor), in a match
    of a value derived from the parameter -- by such patterns' binders,
    lets, and coercions [in_place] says keep the value's representation --
    each perhaps through a coercion so.  A copy of a derived value shares
    the pointers it holds.  What the body of a loop an entry enters reads
    of the scope is a copy a frame kept, stored so only where it is the
    handle of a cell ([cell_fields] gives the fields holding their value in
    one), not where the field holds the value itself.  [false] for each
    where no call continues [l]. *)
val parts_passed :
  pointer_fields:(Names.GlobRef.t -> int list option) ->
  cell_fields:(Names.GlobRef.t -> int list option) ->
  in_place:(Core.Type.t -> Core.Type.t -> bool) ->
  loop ->
  bool list

(** For each parameter of the loop [l], outermost first, whether every
    [Continue] of [l] passes it a value derived from one of [l]'s
    parameters, as {!parts_passed} derives one: the parameter, a field of
    it, either stored in what the caller passed or held inside such a value.
    A value made in a turn -- a call's result, a binder of a match on one --
    is derived from none.  [false] for each where no call continues [l]. *)
val derived_passed :
  pointer_fields:(Names.GlobRef.t -> int list option) ->
  in_place:(Core.Type.t -> Core.Type.t -> bool) ->
  loop ->
  bool list

(** A turn passing a parameter a value it makes: the [Continue] made of
    [turn], and whether another of its arguments reads that parameter or a
    binder derived from it. *)
type rebuilt = {
  turn : Core.Occurrence.t;
  read_elsewhere : bool;
}

(** The [Continue]s of the loop [l], in order, passing its parameter [i] a
    value derived from none of [l]'s parameters, as {!derived_passed}
    derives one: a value made in the turn, which a parameter kept as a
    pointer cannot point at past it. *)
val rebuilt :
  pointer_fields:(Names.GlobRef.t -> int list option) ->
  in_place:(Core.Type.t -> Core.Type.t -> bool) ->
  loop ->
  int ->
  rebuilt list
