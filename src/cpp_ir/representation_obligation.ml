(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

type t =
  | Unresolved_type
  | Opaque_type
  | Unspellable_binder
  | Unsettled_callable
  | Unresolved_cast
  | Free_type_variable
  | Implicit_boxed_read
  | Missing_template_argument
  | Unlowered_method_call
  | Unlowered_projection
  | Unlowered_conditional
  | Move_under_access
  | Undecided_constexpr
  | Uninstantiated_mapping
  | Unlowered_qualifier
  | Unslotted_pointer
  | Unnamed_scrutinee
  | Undecided_capture
  | Capture_outside_a_block

let all =
  [ Unresolved_type; Opaque_type; Unspellable_binder; Unsettled_callable; Unresolved_cast; Free_type_variable;
    Implicit_boxed_read; Missing_template_argument; Unlowered_method_call; Unlowered_projection;
    Unlowered_conditional; Move_under_access; Undecided_constexpr; Uninstantiated_mapping; Unlowered_qualifier;
    Unslotted_pointer; Unnamed_scrutinee; Undecided_capture; Capture_outside_a_block ]
