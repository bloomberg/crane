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
    just its one argument stands for that argument.  A function in a
    recursive group with partners ({!Recursive_groups}) is planned as its
    group: every call between members counts, as it does once Loopify has
    inlined the partners into it. *)

type kind =
  | No_recursion
  | Tail  (** every recursive call is a tail call *)
  | Nontail  (** some recursive call is not *)

type t

val empty : t

(** [analyze groups s] plans every function [s] defines, in the recursive
    groups [groups]. *)
val analyze : Recursive_groups.t -> Miniml.ml_structure -> t

val equal : t -> t -> bool

(** Make [t] the extraction's plan, the one {!find} reads. *)
val install : t -> unit

(** The kind of the function [r], if the program defines it. *)
val find : Names.GlobRef.t -> kind option
