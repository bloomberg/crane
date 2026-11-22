(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What a position asks of the value put in it ({!Grammar.Slot_type}). *)

include Grammar.Slot_type

(** The slot of a parameter passed in mode [m] and declared at [t]: the
    value type it stands for when taken by value or by reference, the
    forwarding reference a deduced callable is, or a typed mapping's
    view. *)
let of_param (m : Param_mode.t) (t : 'p Type.t) : 'p t =
  match m.form with
  | By_value | By_const_value | By_const_reference | By_reference -> Exactly (Param_mode.value_type m t)
  | By_forwarding_reference -> Forwarded
  | By_view (v, r) -> View (v, r)
