(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The C++ type each coercion's position is generated against, planned
    from Core ahead of lowering.

    A coercion ([MLmagic]) is lowered against the type of the position it
    fills: the parameter a global call passes it at, the return type of the
    region whose result it is, a constructor's field.  The plan walks a
    region's Core body and gives each coercion's occurrence that type, by
    the decisions lowering makes for each position
    ({!Translation_calls.plan_call}, {!Translation_calls.argument_position},
    {!Translation_constructors.regular_field},
    {!Translation_constructors.record_field},
    {!Translation_constructors.custom_field}), carrying the slot each value
    is built into as lowering threads it.  A lambda's body is planned as a
    region of its own, where its return type is known.  A position that
    states no type is planned at none. *)

(** [region ~outer ~reads body] -- the planned position type of each
    coercion in [body], a region generated in the binders [outer] under the
    return type in force, its variable reads planned as [reads]. *)
val region :
  outer:Lexenv.t ->
  reads:(Miniml.Occurrence.t * Translation_state.planned_read) list ->
  Miniml.ml_ast ->
  (Miniml.Occurrence.t * Minicpp.cpp_type option) list
