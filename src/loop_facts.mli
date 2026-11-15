(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What loop lowering ({!Control_to_cpp_ir}, Loopify) reads of the
    analysis of the program and of the unit being lowered: the input of the
    finishing passes that turn recursion into loops, as {!Translation_state}'s
    is lowering's.  Those passes may not depend on translation, nor can
    translation name the plans' types ({!Recursion_plan} reads translation's
    suspension rules), so the facts are set here, for the extent of the
    program's units and then of each unit, by the driver that analysed
    them; outside that extent every fact is that of a program that defines
    nothing. *)

type t = {
  recursion : Recursion_plan.t;  (** how each function recurses *)
  control : Lower_control.t;  (** the loops that recursion lowers to *)
  effects : Core_effects.t;
      (** the effect operations of the unit being lowered, which a loop's
          turns read as its statements ({!Ownership_ir.continue_moves}) *)
}

(** [with_program ~recursion ~control f] runs [f] lowering the units of a
    program whose recursion plan is [recursion] and whose loops are
    [control]. *)
val with_program : recursion:Recursion_plan.t -> control:Lower_control.t -> (unit -> 'a) -> 'a

(** [with_unit ~effects f] runs [f] lowering a unit, of the program being
    lowered, whose effect operations are [effects]. *)
val with_unit : effects:Core_effects.t -> (unit -> 'a) -> 'a

(** The program's recursion plan. *)
val recursion : unit -> Recursion_plan.t

(** The program's loops. *)
val control : unit -> Lower_control.t

(** The unit's effect operations. *)
val effects : unit -> Core_effects.t
