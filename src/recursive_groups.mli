(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The recursive groups of a frozen program: the strongly connected components of its call graph over
    the functions it defines, a function that refers to itself counted as a
    group of its own.  A fact about the Core program, computed once from it
    ({!Program_facts.analyze_program}), and the first part of a recursion
    plan: which functions recurse through which, before any is lowered.
    Loopify takes the partners it inlines into a function from here.

    A function is a node under the name it is defined with; an edge is a
    reference to a defined function anywhere in a body, applied or not.  A
    helper lifted out of a body later is part of that body here. *)

open Names

(** Each defined function on a cycle, mapped to its group. *)
type t

(** No groups. *)
val empty : t

(** The groups of the functions [struc] defines, over every term definition
    in it, module and functor bodies included. *)
val analyze : Miniml.ml_structure -> t

(** The members of the group of [r], [r] among them, if [r] is on a cycle. *)
val group : t -> GlobRef.t -> GlobRef.t list option

(** Every group, each one's members in definition order. *)
val groups : t -> GlobRef.t list list

(** Whether [r'] is in the group of [r]: [r] is on a cycle and [r'] is one
    of its members, [r] itself among them. *)
val in_group : t -> GlobRef.t -> GlobRef.t -> bool

(** Same groups, member for member. *)
val equal : t -> t -> bool

(** Make [t] the extraction's recursive groups, for the passes that still
    read them from a table. *)
val install : t -> unit

(** The groups last {!install}ed in this extraction, {!empty} before. *)
val installed : unit -> t
