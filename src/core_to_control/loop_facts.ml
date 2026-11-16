(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What loop lowering reads of the program's and the unit's analysis.  See
    [loop_facts.mli]. *)

type t = {
  recursion : Core_plan.Recursion.t;
  control : Lower_control.t;
  effects : Core_plan.Effects.t;
}

let none = {recursion = Core_plan.Recursion.empty; control = Lower_control.empty; effects = Core_plan.Effects.empty}
