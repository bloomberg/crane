(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** How each function of a frozen program recurses
    (docs/Pipeline-Disentangling-Plan.md, Milestone 6), read off its Core
    body before any function is lowered: a fact about the program
    ({!Program_facts.analyze_program}), and what Loopify transforms a
    function by.

    A call is a tail call where the function's result is the call's.  The
    effect operations are read as {!Core_effects} elaborates them: in a
    sequential computation the continuation of a [bind] and the value of a
    [ret] stand where the operation does.  A custom whose replacement text is
    just its one argument stands for that argument.  The plan is per
    recursive group ({!Recursive_groups}), exactly one each: every call
    between members counts, as it does once Loopify has inlined the partners
    into a member.  A function on no cycle does not recurse.

    For a function that does not recurse only by tail calls, the plan also
    reads the constructors its result is built of around its calls, which
    decide whether it is lowered tail modulo cons ({!strategy}). *)

type kind =
  | No_recursion
  | Tail  (** every recursive call is a tail call *)
  | Nontail  (** some recursive call is not *)

(** A recursive group's plan: its members, in definition order, and how
    the group recurses. *)
type group = private {
  members : Names.GlobRef.t list;
  kind : kind;
}

type t

val empty : t

(** [analyze groups s] plans every function [s] defines, in the recursive
    groups [groups]. *)
val analyze : Recursive_groups.t -> Miniml.ml_structure -> t

val equal : t -> t -> bool

(** Make [t] the extraction's plan, the one {!strategy} reads. *)
val install : t -> unit

(** The plan of the group of the function [r], if [r] is on a cycle. *)
val group_of : Names.GlobRef.t -> group option

(** A constructor applied around a recursive call: its argument [hole], in
    the constructor's declared order, holds the call. *)
type cell = private {
  constructor : Names.GlobRef.t;
  hole : int;
}

(** The constructors around one recursive call, outermost first, the
    innermost holding the call itself. *)
type chain = private {
  around : cell list;
  innermost : cell;
}

(** How a function's recursion is lowered, one per function. *)
type strategy =
  | No_loop  (** it does not recurse *)
  | Tail_loop  (** every recursive call is a tail call, and becomes a jump *)
  | Modulo_cons of chain list
      (** tail modulo cons: each call that is not a tail call is the one
          call of one of these chains, all ending in the same cell, which is
          left empty and filled by the next turn of the loop; there is at
          least one *)
  | Frame_stack  (** some call is not a tail call: an explicit stack *)

(** The kind of recursion a strategy lowers. *)
val kind_of_strategy : strategy -> kind

(** The strategy of the function [r], if the program defines it: its
    group's kind, [No_recursion] off every cycle, and for a member that does
    not recurse only by tail calls whether it is lowered tail modulo cons.
    It is, where each call that is not a tail call is the one call of a
    chain of constructor applications in tail position, the innermost
    holding it directly, read off [r]'s Core body with {!Normalize}'s
    temporaries put back and its partners inlined as Loopify inlines them.
    Every chain ends in the same constructor, holding the call at the same
    argument, which its constructor stores behind the pointer, and every
    constructor in a chain stores some field there: [pointer_fields c] are
    the arguments of [c] so stored, [None] where it stores none
    ({!Gen_inductives.constructor_pointer_fields}). *)
val strategy :
  pointer_fields:(Names.GlobRef.t -> int list option) -> Names.GlobRef.t -> strategy option

(** The strategy of the local fixpoint bound to [binder] in the definition
    [origin], if [origin] defines one: planned from its body as a
    definition's is, every call between the members of its group counting.
    A helper lifted out of [origin] for that fixpoint is planned by it
    ({!Lifted}).  Where two fixpoints bind the same name in one definition,
    both count: the kind is the stronger, and the chains both's where they
    end in the same cell. *)
val strategy_local :
  pointer_fields:(Names.GlobRef.t -> int list option) ->
  origin:Names.GlobRef.t ->
  binder:Names.Id.t ->
  strategy option
