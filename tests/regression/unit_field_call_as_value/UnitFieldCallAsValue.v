(** Crane bug: calling a unit-returning record field ([globals_set : nat ->
    unit], emitted [std::function<void(Nat)>]) in a *value* position puts a
    [void] expression into a pair.

    Observed (post-pattern_binder_state_boxed install):
      std::pair<Nat, std::monostate> UnitFieldCallAsValue::update(const Nat &gs) {
        return std::make_pair(gs, globals_object.globals_set(gs));
    Diagnostic:
      error: no matching function for call to 'make_pair'
      note: substitution failure [with _T1 = ..., _T2 = void]: cannot form a
            reference to 'void'
    The call's [void] needs to be sequenced and replaced by
    [std::monostate{}] (or the field typed to return [std::monostate]).

    Reduced from Vellvm, [Semantics/Handlers/Global.v:51-60]
    ([Record debug_globals := { globals_set : map -> unit ; ... }],
    [update_globals_ref := fun gs => ret (gs, globals_object.(globals_set) gs)]);
    [Handlers/Local.v]'s [update_locals_ref] is the same.  2 of Vellvm's 8
    remaining errors. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module UnitFieldCallAsValue.
  (* Vellvm's Handlers/Global.v: a record of unit-returning hooks. *)
  Record debug_globals : Type := mk_debug_globals { globals_set : nat -> unit ; globals_get : unit -> nat }.
  Definition globals_object : debug_globals := {| globals_set := fun _ => tt ; globals_get := fun _ => 0 |}.

  (* [update_globals_ref := fun gs => ret (gs, globals_object.(globals_set) gs)] *)
  Definition update (gs : nat) : nat * unit := (gs, globals_object.(globals_set) gs).

  Definition is_three : bool := Nat.eqb (fst (update 3)) 3.
End UnitFieldCallAsValue.

Crane Extraction "unit_field_call_as_value" UnitFieldCallAsValue.
