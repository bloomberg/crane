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
  Monads.STMonadTactics
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

  Transparent HAList.halist_lookup HAList.halist_add HAList.HMap_halist HAList.HMapOk_halist.
  Opaque add lookup STRefToIx zero suc.
  Lemma fib_loop_correct :
    forall k (a b : nat) (m : mem) (x y : STRef S nat),
    lookup (STRefToIx S nat x, zero) m = Some a ->
    lookup (STRefToIx S nat y, suc zero) m = Some b ->
    fmap snd (interp_st ltu nat (fib_loop k x y zero (suc zero)) m)
    ≈ Ret (fib_seq a b k).
  Proof.
    induction k; intros a b m x y hx hy; simpl fib_loop.
    - etransitivity.
      { eapply eutt_fmap. repeat stforward. rewrite hx. reflexivity. }
      setoid_rewrite map_ret. reflexivity.
    - etransitivity.
      { eapply eutt_fmap. repeat stforward_refine. reflexivity. }
      setoid_rewrite map_bind. rewrite hx.
      monad_simpl_inner.
      setoid_rewrite map_bind. rewrite hy.
      repeat setoid_rewrite bind_Ret_l.
      apply IHk.
      + etransitivity; [ apply hmap_lookup_add_ne; intros [=] |].
        rewrite mapsto_lookup. apply mapsto_add_eq. Unshelve. all: try typeclasses eauto.
      + rewrite mapsto_lookup. apply mapsto_add_eq. Unshelve. all: try typeclasses eauto.
  Qed.

  Lemma fib_ST_full_correct : forall n,
    fmap snd (interp_st (S := S) ltu nat
      (x <- newSTRef zero 0;; y <- newSTRef (suc zero) 1;; fib_loop n x y zero (suc zero))
      HMap.empty)
    ≈ Ret (fib_seq 0 1 n).
  Proof.
    intro n.
    etransitivity.
    { eapply eutt_fmap. repeat stforward_refine. reflexivity. }
    setoid_rewrite map_bind.
    monad_simpl_inner.
    apply fib_loop_correct.
    + etransitivity; [ apply hmap_lookup_add_ne; intros [=] |].
      rewrite mapsto_lookup. apply mapsto_add_eq. Unshelve. all: try typeclasses eauto.
    + rewrite mapsto_lookup. apply mapsto_add_eq. Unshelve. all: try typeclasses eauto.
  Qed.

End FibonacciProofs.

Lemma fib_ST_eq_fib_fun : forall {S : Type} (n : nat),
    ret (fib_fun n) ≈ runST (S := S) (fun S0 => fib_ST n).
Proof.
  intros S n. unfold runST, fib_ST. symmetry.
  destruct (Nat.ltb_spec n 2) as [Hn | Hn].
  - etransitivity.
    { eapply eutt_fmap. change_to_monad. rewrite interp_st_ret. reflexivity. }
    setoid_rewrite map_ret. apply eqit_Ret.
    destruct n as [|[|n]]; [ reflexivity | reflexivity | lia ].
  - rewrite fib_fun_eq_seq. exact (@fib_ST_full_correct unit n).
Qed.
