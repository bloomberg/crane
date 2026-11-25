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
  Monads.Indices
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

  Let T := nat.
  Let ltu := Nat.le.
  Existing Instance nat_ix_correct.
  Existing Instance nat_ix_stref.
  Context {S : Type}.
  Let V : T -> Type := fun _ => nat.

  (** The two references have different indices ([zero] and [suc zero]), so
      a write to one leaves the other's cell alone. *)
  Lemma fib_loop_spec :
    forall k (a b : nat) (m : @mem nat V) (x y : STRef S nat),
    st_lookup V (STRefToIx S nat x, zero) m = Some a ->
    st_lookup V (STRefToIx S nat y, suc zero) m = Some b ->
    st_spec (E := exceptE Err) (fib_loop k x y zero (suc zero)) m
      (fun _ r => r = fib_seq a b k).
  Proof.
    induction k as [|k IH]; intros a b m x y hx hy; cbn [fib_loop].
    - eapply (st_spec_readSTRef (V := V) zero); [ exact hx | reflexivity ].
    - apply st_spec_bind. eapply (st_spec_readSTRef (V := V) zero); [ exact hx |]. cbv beta.
      apply st_spec_bind. eapply (st_spec_readSTRef (V := V) (suc zero)); [ exact hy |]. cbv beta.
      apply st_spec_bind, (st_spec_writeSTRef (V := V) zero). cbv beta.
      apply st_spec_bind, (st_spec_writeSTRef (V := V) (suc zero)). cbv beta.
      apply IH.
      + rewrite hmap_lookup_add_ne by (intros [= _ H]; discriminate H).
        exact (hmap_lookup_add_eq (V := idx_key_type V) _ _ _).
      + exact (hmap_lookup_add_eq (V := idx_key_type V) _ _ _).
  Qed.

End FibonacciProofs.

Lemma fib_ST_eq_fib_fun : forall {S : Type} (n : nat),
    Ret (fib_fun n) ≈ runST (S := S) (fun S0 => fib_ST n).
Proof.
  intros S n.
  destruct (st_spec_runST (S := S) (fun S0 => fib_ST (S := S0) n) (fun r => r = fib_fun n))
    as (r & Hrun & ->); [| symmetry; exact Hrun ].
  unfold fib_ST. destruct (Nat.ltb_spec n 2) as [Hn | Hn].
  - apply st_spec_ret. destruct n as [|[|n]]; [ reflexivity | reflexivity | lia ].
  - apply st_spec_bind, (st_spec_newSTRef (V := fun _ => nat) zero). cbv beta.
    apply st_spec_bind, (st_spec_newSTRef (V := fun _ => nat) (suc zero)). cbv beta.
    eapply st_spec_weaken; [| apply fib_loop_spec ].
    + intros _ r ->. symmetry. apply fib_fun_eq_seq.
    + rewrite hmap_lookup_add_ne by (intros [= _ H]; discriminate H).
      exact (hmap_lookup_add_eq (V := idx_key_type (fun _ : nat => nat)) _ _ _).
    + exact (hmap_lookup_add_eq (V := idx_key_type (fun _ : nat => nat)) _ _ _).
Qed.
