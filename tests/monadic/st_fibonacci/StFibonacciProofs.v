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

From Crane Require Import
  Monads.Error
  Monads.ITree
  Monads.MonadFacts
  Monads.STMonad
  Monads.STMonadFacts
  Monads.STMonadSpec
  Utils.HMap
.

From CraneTestsMonadic.st_fibonacci Require Import StFibonacci.

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
    forall k (a b : nat) (m : mem V) (x y : nat),
    x <> y -> st_get x m = Some a -> st_get y m = Some b ->
    st_spec (E := exceptE Err) (fib_loop (R := model_refs) k x y) m
      (fun _ r => r = fib_seq a b k).
  Proof.
    induction k as [|k IH]; intros a b m x y Hxy hx hy; cbn [fib_loop].
    - eapply st_spec_readSTRef; [ exact hx | reflexivity ].
    - apply st_spec_bind. eapply st_spec_readSTRef; [ exact hx |]. cbv beta.
      apply st_spec_bind. eapply st_spec_readSTRef; [ exact hy |]. cbv beta.
      apply st_spec_bind, st_spec_writeSTRef. cbv beta.
      apply st_spec_bind, st_spec_writeSTRef. cbv beta.
      apply IH; [ exact Hxy | | ].
      + rewrite st_get_put_ne by exact Hxy. apply st_get_put_eq.
      + apply st_get_put_eq.
  Qed.

End FibonacciProofs.

Lemma fib_ST_eq_fib_fun : forall (n : nat),
    Ret (fib_fun n) ≈ runST (fun R => fib_ST (R := R) n).
Proof.
  intros n.
  destruct (st_spec_runST (fun R => fib_ST (R := R) n) (fun r => r = fib_fun n))
    as (r & Hrun & ->); [| symmetry; exact Hrun ].
  unfold fib_ST. destruct (Nat.ltb_spec n 2) as [Hn | Hn].
  - apply st_spec_ret. destruct n as [|[|n]]; [ reflexivity | reflexivity | lia ].
  - apply st_spec_bind, st_spec_newSTRef. cbv beta.
    apply st_spec_bind, st_spec_newSTRef. cbv beta.
    set (m1 := st_put _ 0 _).
    (* the second location is past the first, which is in use *)
    assert (Hfresh : st_fresh (V := fun _ : nat => nat) HMap.empty <> st_fresh m1).
    { intros Heq. assert (Hin : st_get (V := fun _ : nat => nat) (st_fresh HMap.empty) m1 = Some 0)
        by apply st_get_put_eq.
      rewrite Heq, st_get_fresh in Hin by lia. discriminate. }
    eapply st_spec_weaken; [| apply fib_loop_spec; [ exact Hfresh | | ] ].
    + intros _ r ->. symmetry. apply fib_fun_eq_seq.
    + rewrite st_get_put_ne by exact Hfresh. apply st_get_put_eq.
    + apply st_get_put_eq.
Qed.
