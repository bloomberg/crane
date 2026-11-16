(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What loop lowering ({!Control_to_cpp_ir}, {!Loopify}) reads of the
    analysis of the program and of the unit being lowered: the input of the
    passes that turn recursion into loops (ControlIR), as
    {!Translation_state}'s is lowering's.  A field of the unit's context
    ({!Unit_plan.Context.t.loops}): the program's, from
    {!Program_facts.analyze_program}, with the unit's effect operations,
    from {!Program_facts.analyze}. *)

type t = {
  recursion : Core_plan.Recursion.t;  (** how each function recurses *)
  control : Lower_control.t;  (** the loops that recursion lowers to *)
  effects : Core_plan.Effects.t;
      (** the effect operations of the unit being lowered, which a loop's
          turns read as its statements ({!Ownership_ir.continue_moves}) *)
}

(** The facts of a program that defines nothing. *)
val none : t
