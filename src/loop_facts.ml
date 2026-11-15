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

(* Set only for a dynamic extent, and restored however it is left. *)
let current = ref none

let with_facts t f =
  let saved = !current in
  current := t;
  Fun.protect ~finally:(fun () -> current := saved) f

let with_program ~recursion ~control f = with_facts {!current with recursion; control} f
let with_unit ~effects f = with_facts {!current with effects} f
let recursion () = !current.recursion
let control () = !current.control
let effects () = !current.effects
