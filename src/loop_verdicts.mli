(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What control lowering did with each loop it decided on
    (docs/Pipeline-Disentangling-Plan.md, Milestone 6): the record the
    finished program is checked against under [CRANE_CHECK_IR]
    ({!Control_to_legacy_minicpp.check_lowered}), in place of running Loopify
    again to see what it would change.  Written only while the checks run,
    for one generated file. *)

type t =
  | Lowered  (** made the loop the recursion plan commits to *)
  | Declined of string
      (** made no loop of it, for this reason, read off the program's Core
          and its ControlIR before any C++ was lowered: a turn passing a
          receiver it makes, which a pointer kept across turns cannot point
          at *)
  | Unlowered of string
      (** left the definition as it was generated, for this reason, though
          the plan commits to a loop of it and nothing before lowering
          declined it: under [CRANE_CHECK_IR] a violation *)
  | Kept
      (** a local fixpoint or a method left as generated where the plan
          commits to no loop of it there: one a machine may adopt, one
          lowered with the machine it is in, one its loop's turns never
          continue *)

(** [record l v] makes [v] the verdict on the loop [l], replacing any
    earlier one: a definition generated again is decided again, alike. *)
val record : Control_ir.Loop.t -> t -> unit

(** The verdict on the loop [l], if one was recorded. *)
val find : Control_ir.Loop.t -> t option
