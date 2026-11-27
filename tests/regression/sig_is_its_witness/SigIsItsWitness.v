(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A [sig] is its witness ([Mapping.Shared]'s [sig_mapping]), in each
    position its value can take. *)

From Stdlib Require Import Arith.PeanoNat Lia List.
From Crane Require Import Mapping.Std Mapping.NatInt.
Import ListNotations.

Module SigIsItsWitness.

(** A plain witness, built, projected and matched. *)
Definition pos (n : nat) : {m : nat | 0 < m} := exist _ (S n) (Nat.lt_0_succ n).
Definition pos_val (n : nat) : nat := proj1_sig (pos n).
Definition pos_match (n : nat) : nat := let (m, _) := pos n in m + 1.

(** Nested: a sig of a sig. *)
Definition nested (n : nat) : {p : {m : nat | 0 < m} | proj1_sig p > n} :=
  exist _ (pos n) (Nat.lt_succ_diag_r n).
Definition nested_val (n : nat) : nat := proj1_sig (proj1_sig (nested n)).

(** A function as the witness. *)
Definition fixes_zero : {f : nat -> nat | f 0 = 0} := exist _ (fun x => x * 2) eq_refl.
Definition apply_fixes_zero (n : nat) : nat := proj1_sig fixes_zero n.

(** [unit] as the witness. *)
Definition unit_sig : {u : unit | u = tt} := exist _ tt eq_refl.
Definition unit_sig_used (n : nat) : nat := let (u, _) := unit_sig in match u with tt => n end.

(** A type variable as the witness. *)
Definition wrap {A : Type} (x : A) : {y : A | y = x} := exist _ x eq_refl.
Definition unwrap_list (xs : list nat) : list nat := proj1_sig (wrap xs).

(** Witnesses in a container. *)
Fixpoint positives (k : nat) : list {m : nat | 0 < m} :=
  match k with O => [] | S k' => pos k' :: positives k' end.
Definition sum_positives (k : nat) : nat :=
  fold_left (fun acc p => acc + proj1_sig p) (positives k) 0.

(** A recursive inductive whose constructor holds a sig of itself. *)
Inductive rt : Type :=
| Leaf : rt
| Node : {r : rt | True} -> nat -> rt.
Fixpoint rt_sum (t : rt) : nat :=
  match t with
  | Leaf => 0
  | Node (exist _ r _) n => n + rt_sum r
  end.
Definition rt_example : rt := Node (exist _ (Node (exist _ Leaf I) 3) I) 4.
Definition rt_example_sum : nat := rt_sum rt_example.

(** [sig2]. *)
Definition between (n : nat) : {m : nat | n <= m & m <= n + 1} :=
  exist2 _ _ n (Nat.le_refl n) (Nat.le_add_r n 1).
Definition between_val (n : nat) : nat := let (m, _, _) := between n in m.

End SigIsItsWitness.

Crane Extraction "sig_is_its_witness" SigIsItsWitness.
