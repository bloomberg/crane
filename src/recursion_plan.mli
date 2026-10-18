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
    decide whether it is lowered tail modulo cons ({!modulo_cons}). *)

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

(** Make [t] the extraction's plan, the one {!find} reads. *)
val install : t -> unit

(** The plan of the group of the function [r], if [r] is on a cycle. *)
val group_of : Names.GlobRef.t -> group option

(** The kind of the function [r], if the program defines it: its group's,
    or [No_recursion] off every cycle. *)
val find : Names.GlobRef.t -> kind option

(** The kind of the local fixpoint bound to [binder] in the definition
    [origin], if [origin] defines one: the kind of the fixpoint's group,
    planned from its body as a definition's is, every call between its
    members counting.  A helper lifted out of [origin] for that fixpoint is
    planned by it ({!Lifted}).  Two fixpoints binding the same name in one
    definition both count. *)
val find_local : origin:Names.GlobRef.t -> binder:Names.Id.t -> kind option

(** Whether the recursion of the function [r] is lowered tail modulo cons,
    if the program defines [r]: [r] does not recurse only by tail calls, and
    each call that is not one is the one call of a chain of constructor
    applications in tail position, the innermost holding it directly, read
    off [r]'s Core body with {!Normalize}'s temporaries put back and its
    partners inlined as Loopify inlines them.  Every chain ends in the same
    constructor, holding the call at the same argument, which its
    constructor stores behind the pointer, and every constructor in a chain
    stores some field there: [pointer_fields c] are the arguments of [c] so
    stored, [None] where it stores none
    ({!Gen_inductives.constructor_pointer_fields}). *)
val modulo_cons :
  pointer_fields:(Names.GlobRef.t -> int list option) -> Names.GlobRef.t -> bool option

(** {!modulo_cons} of the local fixpoint bound to [binder] in the definition
    [origin], read off its body as a definition's is, if [origin] defines
    one; where two fixpoints bind the same name there, both must lower. *)
val modulo_cons_local :
  pointer_fields:(Names.GlobRef.t -> int list option) ->
  origin:Names.GlobRef.t ->
  binder:Names.Id.t ->
  bool option
