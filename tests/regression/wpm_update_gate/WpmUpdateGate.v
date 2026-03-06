(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: conditional ROM update at latched address on WPM. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module WpmUpdateGate.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: xs => y :: update_nth n' x xs
  | _, [] => []
  end.

Record state : Type := mkState {
  rom : list nat;
  prom_addr : nat;
  prom_data : nat;
  prom_enable : bool
}.

Definition execute_wpm (s : state) : state :=
  let new_rom := if prom_enable s
                 then update_nth (prom_addr s) (prom_data s) (rom s)
                 else rom s in
  mkState new_rom (prom_addr s) (prom_data s) (prom_enable s).

Definition t : nat :=
  let s := mkState [10; 11; 12] 1 99 true in
  let s' := execute_wpm s in
  nth 1 (rom s') 0.

End WpmUpdateGate.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "wpm_update_gate" WpmUpdateGate.
