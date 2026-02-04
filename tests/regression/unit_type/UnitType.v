(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Test unit type extraction *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module UnitType.

(* Unit value *)
Definition unit_val : unit := tt.

(* Function returning unit *)
Definition return_unit (n : nat) : unit := tt.

(* Function taking unit *)
Definition take_unit (u : unit) : nat := five.

(* Pattern match on unit *)
Definition match_unit (u : unit) : nat :=
  match u with
  | tt => seven
  end.

(* Unit in a product *)
Inductive pair (A B : Type) : Type :=
| Pair : A -> B -> pair A B.

Arguments Pair {A B} _ _.

Definition pair_with_unit : pair nat unit := Pair three tt.
Definition unit_pair : pair unit unit := Pair tt tt.

(* Function with unit in signature *)
Definition unit_to_unit (u : unit) : unit := u.

(* Sequence operations (simulating side effects) *)
Definition seq {A B : Type} (a : A) (b : B) : B := b.

Definition sequenced : nat :=
  seq tt (seq tt five).

(* Test values *)
Definition test_take := take_unit tt.
Definition test_match := match_unit tt.
Definition test_seq := sequenced.

End UnitType.

Crane Extraction "unit_type" UnitType.
