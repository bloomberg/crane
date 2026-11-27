(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [fib_ST] computes [fib_fun]: the loop is modelled by [fib_seq]. *)

From Stdlib Require Import
  Arith.PeanoNat
  Lia
.

From ExtLib Require Import
  Structures.Functor
  Structures.Monad
.

From ITree Require Import
  Events.Exception
  ITree
  ITreeFacts
.

From Crane Require Monads.ST.
From Crane Require Import
  Monads.Error
  Monads.ITree
  Monads.MonadFacts
  Monads.STFacts
  Monads.STSpec
  Utils.HMap
.

From CraneTestsMonadic.st_fibonacci Require Import STFibonacci.

Import Monads.
Local Open Scope monad_scope.

(** [k] steps of [(a, b) := (b, a + b)], returning [a]. *)
Fixpoint fib_seq (a b k : nat) : nat :=
  match k with
  | 0 => a
  | Datatypes.S k' => fib_seq b (a + b) k'
  end.

Lemma fib_seq_add : forall n a b c d,
  fib_seq a b n + fib_seq c d n = fib_seq (a + c) (b + d) n.
Proof. induction n; intros; simpl; [lia | rewrite IHn; f_equal; lia]. Qed.

Lemma fib_fun_eq_seq : forall n, fib_fun n = fib_seq 0 1 n.
Proof.
  enough (forall n, fib_fun n = fib_seq 0 1 n
                    /\ fib_fun (Datatypes.S n) = fib_seq 0 1 (Datatypes.S n))
    as H by (intro n; exact (proj1 (H n))).
  induction n as [|n [IH1 IH2]]; [split; reflexivity |].
  split; [exact IH2 |].
  change (fib_fun (Datatypes.S (Datatypes.S n))) with (fib_fun (Datatypes.S n) + fib_fun n).
  rewrite IH1, IH2. apply (fib_seq_add n 1 1 0 1).
Qed.

Section FibonacciProofs.

  Notation V := (fun _ : nat => nat).

  (** [x] and [y] are different locations, holding [a] and [b]. *)
  Lemma fib_loop_spec :
    forall k (a b : nat) (m : ST.mem V) (x y : nat),
    x <> y -> read_at x m = Some a -> read_at y m = Some b ->
    spec (E := exceptE Err) (fib_loop (R := ST.model_refs) k x y) m
      (fun _ r => r = fib_seq a b k).
  Proof.
    induction k as [|k IH]; intros a b m x y Hxy hx hy; cbn [fib_loop].
    - eapply read_ref; [ exact hx | reflexivity ].
    - apply spec_bind. eapply read_ref; [ exact hx |]. cbv beta.
      apply spec_bind. eapply read_ref; [ exact hy |]. cbv beta.
      apply spec_bind, write_ref. cbv beta.
      apply spec_bind, write_ref. cbv beta.
      apply IH; [ exact Hxy | | ].
      + rewrite read_at_write_at_ne by exact Hxy. apply read_at_write_at_eq.
      + apply read_at_write_at_eq.
  Qed.

End FibonacciProofs.

Lemma fib_ST_eq_fib_fun : forall (n : nat),
    Ret (fib_fun n) ≈ ST.run (fun R => fib_ST (R := R) n).
Proof.
  intros n.
  destruct (run (fun R => fib_ST (R := R) n) (fun r => r = fib_fun n))
    as (r & Hrun & ->); [| symmetry; exact Hrun ].
  unfold fib_ST. destruct (Nat.ltb_spec n 2) as [Hn | Hn].
  - apply spec_ret. destruct n as [|[|n]]; [ reflexivity | reflexivity | lia ].
  - apply spec_bind, new_ref. cbv beta.
    apply spec_bind, new_ref. cbv beta.
    set (m1 := write_at _ 0 _).
    (* the second location is past the first, which is in use *)
    assert (Hfresh : ST.fresh (V := fun _ : nat => nat) HMap.empty <> ST.fresh m1).
    { intros Heq. assert (Hin : read_at (V := fun _ : nat => nat) (ST.fresh HMap.empty) m1 = Some 0)
        by apply read_at_write_at_eq.
      rewrite Heq, read_at_fresh in Hin by lia. discriminate. }
    eapply spec_weaken; [| apply fib_loop_spec; [ exact Hfresh | | ] ].
    + intros _ r ->. symmetry. apply fib_fun_eq_seq.
    + rewrite read_at_write_at_ne by exact Hfresh. apply read_at_write_at_eq.
    + apply read_at_write_at_eq.
Qed.
