(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What each parameter of each generated function does with the value it
    is given, beside whether it owns it ({!Ownership}).

    A parameter's requirement is a point of a finite lattice, an access
    ([Unused < Read_access < Write_access < Replace_access]) and a
    representation ([Preferred < Canonical]), joined over its uses:
    - an argument of a mapped operation, as its contract's [InputUse] says;
    - an argument of a generated function's direct call, as that function's
      summary says of the parameter it is passed at;
    - anything else -- a constructor argument, a returned value, a
      projection's or a match's subject, an argument of a legacy mapping,
      of a closure or of a partial application -- is a canonical read.
    A local bound to a parameter as it is ([let y := x]) is that parameter.
    The summaries are the least fixed point over every function of the
    program, starting from [Unused].

    A function named as a value anywhere -- passed, stored, partially
    applied -- is called through a first-class callable, whose parameters
    take canonical value forms: it is {e pinned}, and
    {!physical} never gives one of its parameters a mutable reference.  Its
    callers read its summary capped at [Read_access], since it holds a copy
    of whatever it writes or replaces. *)

type access = Unused | Read_access | Write_access | Replace_access

type representation = Preferred | Canonical

type requirement = {
  access : access;
  representation : representation;
  invalidates : bool;
      (** whether the use may invalidate a view of the value: a
          replacement, an opaque use, or an operation argument an
          [InvalidatesViews] fact names; joined by disjunction *)
}

(** [Unused], [Preferred], invalidating nothing: the least requirement. *)
val least : requirement

val join : requirement -> requirement -> requirement

val equal : requirement -> requirement -> bool

(** What an argument of a mapped operation passed at [use] requires of the
    parameter it is: [Take] is a canonical read, or a write if
    a [WritesComponent] fact names the argument ([facts], [name]). *)
val of_use :
  ?facts:Base.Mapping_descriptor.operation_fact list -> ?name:string -> Base.Mapping_descriptor.input_use -> requirement

(** [read_off ~settled n body]: the requirement [body], standing under [n]
    parameters, places on each of them, innermost first, reading [settled g]
    for the summary of the generated function [g] (innermost first; [None]
    for a global no summary covers).  A use under a closure -- a lambda, a
    local fixpoint -- is a [Canonical] read at most: the closure holds a
    copy, which may outlive the call.  Where [sequential] (a declaration
    generated in a sequential monad, {!Effects.declaration_mode}), the
    continuation of a bind is the rest of the statements, run in place, and
    is no closure. *)
val read_off : ?sequential:bool -> settled:(Names.GlobRef.t -> requirement list option) -> int -> Core.Expr.t -> requirement list

(** The settled summaries, and the pinned functions. *)
type t = {
  summaries : (Names.GlobRef.t * requirement list) list;
      (** each generated function's, innermost first, for the parameters its
          head declares ({!Base.Type_util.declared_parameters}) *)
  pinned : Core.Ref.User.Set.t;  (** the functions named as values, and the methods *)
}

val empty : t

(** The summaries of [struc]'s functions, settled across calls.  A function
    generated as a method ([receiver r] is the position of its receiver)
    keeps canonical forms, and is pinned with the functions named as
    values. *)
val summarize : ?receiver:(Names.GlobRef.t -> int option) -> Core.Program.t -> t

(** The summary [g]'s callers read: its own, capped at a [Canonical]
    [Read_access] when [g] is pinned (its parameters take no view). *)
val exported : pinned:Core.Ref.User.Set.t -> Names.GlobRef.t -> requirement list -> requirement list

(** The physical form a borrowed parameter of the typed-mapped type [p]
    with requirement [r] takes, when it is not the canonical
    read form.  An owned parameter is taken by value, before this is asked.
    Where [view_allowed] (default false: a pinned function, a lambda, a
    local function), a [Preferred] read takes [p]'s read view and a
    [Preferred] write its writable view, where [p] declares one.  Where
    [reference_allowed] is false, a form that would be a mutable reference
    is a copy by value instead, which the body may write or replace. *)
val physical :
  reference_allowed:bool ->
  ?view_allowed:bool ->
  Base.Mapping_plan.t ->
  requirement ->
  Base.Mapping_plan.physical
