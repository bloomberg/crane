(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What loop lowering reads of the program's and the unit's analysis.  See
    [loop_facts.mli]. *)

type t = {
  recursion : Recursion_plan.t;
  control : Lower_control.t;
  effects : Core_effects.t;
}

let none = {recursion = Recursion_plan.empty; control = Lower_control.empty; effects = Core_effects.empty}
