(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [union_find_ST] computes [union_find_fun], and [find]'s fuel never runs
    out.

    The ST version is related to the functional model of the ST monad by
    [rep]: the array cell of each element holds the node [get] gives in the
    map. Each ST operation preserves [rep] and returns what its pure
    counterpart returns ([find_sim], [union_sim], [same_sim]), stated in the
    [st_spec] logic of [STMonadSpec]. Since both versions use the same fuel,
    this needs only that parents stay in range ([Closed]).

    Fuel is the element count [n]. Parent links form a forest: from every
    element some root is reached ([Inv]), which every operation preserves.
    The nodes on a path to a root are distinct and below [n], so there are
    at most [n] of them ([reach_bound]), and [find_fun n] returns the root
    ([find_fun_root]). *)

From Stdlib Require Import
  Arith.PeanoNat
  Lia
  List
  FSets.FMapFacts
.

From ExtLib Require Import
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

From CraneTestsMonadic.union_find Require Import UnionFind.

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

Module NatMapFacts := FMapFacts.Facts NatMap.

(** The store of the ST version, and its cell at key [k] of array index 0. *)
Notation store := (mem (fun _ : nat => node)).
Notation cell m k := (st_get (V := fun _ : nat => node) k m).
Notation store_add k v m := (st_put (V := fun _ : nat => node) k v m).

Definition par (s : uf) (x : nat) : nat := fst (get s x).

Lemma get_add s x y nd :
  get (NatMap.add x nd s) y = if x =? y then nd else get s y.
Proof.
  unfold get. destruct (Nat.eqb_spec x y).
  - rewrite NatMapFacts.add_eq_o by exact e. reflexivity.
  - rewrite NatMapFacts.add_neq_o by exact n. reflexivity.
Qed.

Lemma par_add s x y nd :
  par (NatMap.add x nd s) y = if x =? y then fst nd else par s y.
Proof. unfold par. rewrite get_add. destruct (x =? y); reflexivity. Qed.

Section Pure.

  Variable n : nat.

  (** Parents of elements below [n] are below [n]. *)
  Definition Closed (s : uf) : Prop := forall x, x < n -> par s x < n.

  Lemma Closed_add s x r k : Closed s -> r < n -> Closed (NatMap.add x (r, k) s).
  Proof. intros Hs Hr y Hy. rewrite par_add. destruct (x =? y); auto. Qed.

  Lemma find_fun_closed f : forall s x, Closed s -> x < n ->
    fst (find_fun f s x) < n /\ Closed (snd (find_fun f s x)).
  Proof.
    induction f as [|f IH]; intros s x Hs Hx; cbn [find_fun]; [ auto |].
    pose proof (Hs x Hx) as Hp. unfold par in Hp.
    destruct (get s x) as [p k]. destruct (p =? x); [ auto |].
    destruct (IH s p Hs Hp) as [Hr Hs']. destruct (find_fun f s p) as [r s'].
    split; [ exact Hr | apply Closed_add; assumption ].
  Qed.

  Lemma union_fun_closed s x y : Closed s -> x < n -> y < n -> Closed (union_fun n s x y).
  Proof.
    intros Hs Hx Hy. unfold union_fun.
    destruct (find_fun_closed n s x Hs Hx) as [Hrx Hs1].
    destruct (find_fun n s x) as [rx s1]. cbn [fst snd] in *.
    destruct (find_fun_closed n s1 y Hs1 Hy) as [Hry Hs2].
    destruct (find_fun n s1 y) as [ry s2]. cbn [fst snd] in *.
    destruct (rx =? ry); [ exact Hs2 |].
    destruct (get s2 rx) as [px kx], (get s2 ry) as [py ky].
    destruct (kx <? ky); [| destruct (ky <? kx)];
      repeat apply Closed_add; assumption.
  Qed.

  Lemma same_fun_closed s x y : Closed s -> x < n -> y < n ->
    Closed (snd (same_fun n s x y)).
  Proof.
    intros Hs Hx Hy. unfold same_fun.
    destruct (find_fun_closed n s x Hs Hx) as [_ Hs1].
    destruct (find_fun n s x) as [rx s1].
    destruct (find_fun_closed n s1 y Hs1 Hy) as [_ Hs2].
    destruct (find_fun n s1 y) as [ry s2]. exact Hs2.
  Qed.

  (** [reach s x k r]: following parents from [x] reaches the root [r] in [k]
      steps. *)
  Inductive reach (s : uf) : nat -> nat -> nat -> Prop :=
  | reach_root x : par s x = x -> reach s x 0 x
  | reach_step x k r : par s x <> x -> reach s (par s x) k r -> reach s x (S k) r.

  Definition Inv (s : uf) : Prop := Closed s /\ forall x, x < n -> exists k r, reach s x k r.

  Lemma Inv_empty : Inv empty_uf.
  Proof. split; intros x Hx; [ exact Hx | exists 0, x; now constructor ]. Qed.

  Lemma reach_is_root s x k r : reach s x k r -> par s r = r.
  Proof. induction 1; auto. Qed.

  Lemma reach_det s x k r : reach s x k r -> forall k' r', reach s x k' r' -> k = k'.
  Proof.
    induction 1 as [x Hx | x k r Hx _ IH]; inversion 1; subst; auto; try contradiction.
    f_equal. eauto.
  Qed.

  Lemma reach_iter s x k r : reach s x k r ->
    forall i, i <= k -> reach s (Nat.iter i (par s) x) (k - i) r.
  Proof.
    intros Hr i. induction i as [|i IH]; intros Hi; [ now rewrite Nat.sub_0_r |].
    specialize (IH ltac:(lia)). replace (k - i) with (S (k - S i)) in IH by lia.
    inversion IH; subst. assumption.
  Qed.

  Lemma iter_closed s x i : Closed s -> x < n -> Nat.iter i (par s) x < n.
  Proof. intros Hs Hx. induction i; cbn; auto. Qed.

  (** The [k] nodes before the root on a path are distinct and below [n]. *)
  Lemma reach_bound s x k r : Closed s -> x < n -> reach s x k r -> k <= n.
  Proof.
    intros Hs Hx Hr.
    enough (Hlen : length (List.map (fun i => Nat.iter i (par s) x) (seq 0 k)) <= length (seq 0 n))
      by (rewrite length_map, !length_seq in Hlen; exact Hlen).
    apply NoDup_incl_length.
    - apply NoDup_map_NoDup_ForallPairs; [| apply seq_NoDup ].
      intros i j Hi Hj Heq. apply in_seq in Hi, Hj.
      pose proof (reach_iter s x k r Hr i ltac:(lia)) as Hri.
      pose proof (reach_iter s x k r Hr j ltac:(lia)) as Hrj.
      rewrite Heq in Hri. pose proof (reach_det _ _ _ _ Hri _ _ Hrj). lia.
    - intros y Hy. apply in_map_iff in Hy as (i & <- & _).
      apply in_seq. split; [ lia | apply iter_closed; assumption ].
  Qed.

  (** Pointing any element at a root keeps every element reaching a root. *)
  Lemma Inv_add s x r k : Inv s -> x < n -> r < n -> par s r = r ->
    Inv (NatMap.add x (r, k) s).
  Proof.
    intros [Hs Hreach] Hx Hrn Hroot. split; [ apply Closed_add; assumption |].
    set (s' := NatMap.add x (r, k) s).
    assert (Hr' : par s' r = r) by (unfold s'; rewrite par_add; destruct (Nat.eqb_spec x r); auto).
    assert (Hx' : exists k r, reach s' x k r).
    { destruct (Nat.eq_dec r x) as [<- | Hne].
      - exists 0, r. now constructor.
      - exists 1, r. assert (par s' x = r) by (unfold s'; rewrite par_add, Nat.eqb_refl; reflexivity).
        constructor; [ congruence | rewrite H; now constructor ]. }
    intros y Hy. destruct (Hreach y Hy) as (k' & r' & Hry). clear Hy.
    induction Hry as [y Hy | y k' r' Hy _ IH];
      (destruct (Nat.eq_dec x y) as [<- | Hne]; [ exact Hx' |]);
      assert (Hpar : par s' y = par s y) by (unfold s'; rewrite par_add, (proj2 (Nat.eqb_neq _ _) Hne); reflexivity).
    - exists 0, y. constructor. congruence.
    - destruct IH as (k'' & r'' & IH). exists (S k''), r''. constructor; rewrite Hpar; assumption.
  Qed.

  Lemma find_fun_reach s x k r : reach s x k r -> forall f, k <= f -> Inv s -> x < n ->
    fst (find_fun f s x) = r /\ Inv (snd (find_fun f s x))
    /\ forall y, par s y = y -> par (snd (find_fun f s x)) y = y.
  Proof.
    induction 1 as [x Hx | x k r Hx Hr IH]; intros f Hf Hinv Hxn.
    - destruct f; cbn [find_fun]; [ auto |].
      unfold par in Hx. destruct (get s x) as [p kx]. cbn in Hx. subst p.
      rewrite Nat.eqb_refl. auto.
    - destruct f as [|f]; [ lia |]. cbn [find_fun].
      pose proof (proj1 Hinv x Hxn) as Hp.
      assert (Hrn := proj1 (find_fun_closed f s (par s x) (proj1 Hinv) Hp)).
      destruct (IH f ltac:(lia) Hinv Hp) as (Hres & Hinv' & Hroots).
      unfold par in Hx, Hp, Hrn, Hres, Hinv', Hroots.
      destruct (get s x) as [p kx] eqn:Hg. cbn in Hx, Hp, Hrn, Hres, Hinv', Hroots.
      rewrite (proj2 (Nat.eqb_neq _ _) Hx).
      destruct (find_fun f s p) as [r' s'']. cbn in *. subst r'.
      split; [ reflexivity | split ].
      + apply Inv_add; auto. apply Hroots. eapply reach_is_root, Hr.
      + intros y Hy. rewrite par_add. destruct (Nat.eqb_spec x y); [| apply Hroots, Hy ].
        subst y. unfold par in Hy. rewrite Hg in Hy. contradiction.
  Qed.

  (** With fuel [n], [find_fun] reaches the root. *)
  Theorem find_fun_root s x : Inv s -> x < n -> exists k, reach s x k (fst (find_fun n s x)).
  Proof.
    intros Hinv Hx. destruct (proj2 Hinv x Hx) as (k & r & Hr). exists k.
    rewrite (proj1 (find_fun_reach s x k r Hr n (reach_bound s x k r (proj1 Hinv) Hx Hr) Hinv Hx)).
    exact Hr.
  Qed.

  Lemma find_fun_inv s x : Inv s -> x < n ->
    fst (find_fun n s x) < n /\ par (snd (find_fun n s x)) (fst (find_fun n s x)) = fst (find_fun n s x)
    /\ Inv (snd (find_fun n s x)) /\ forall y, par s y = y -> par (snd (find_fun n s x)) y = y.
  Proof.
    intros Hinv Hx. destruct (proj2 Hinv x Hx) as (k & r & Hr).
    destruct (find_fun_reach s x k r Hr n (reach_bound s x k r (proj1 Hinv) Hx Hr) Hinv Hx)
      as (Hres & Hinv' & Hroots).
    split; [ apply find_fun_closed; [ apply Hinv | exact Hx ] |].
    rewrite Hres. split; [ apply Hroots; eapply reach_is_root, Hr |]. auto.
  Qed.

  Lemma union_fun_inv s x y : Inv s -> x < n -> y < n -> Inv (union_fun n s x y).
  Proof.
    intros Hinv Hx Hy. unfold union_fun.
    destruct (find_fun_inv s x Hinv Hx) as (Hrx & Hroot_x & Hinv1 & Hroots1).
    destruct (find_fun n s x) as [rx s1]. cbn [fst snd] in *.
    destruct (find_fun_inv s1 y Hinv1 Hy) as (Hry & Hroot_y & Hinv2 & Hroots2).
    destruct (find_fun n s1 y) as [ry s2]. cbn [fst snd] in *.
    specialize (Hroots2 rx Hroot_x).
    destruct (Nat.eqb_spec rx ry); [ exact Hinv2 |].
    destruct (get s2 rx) as [px kx], (get s2 ry) as [py ky].
    destruct (kx <? ky); [| destruct (ky <? kx)]; try (apply Inv_add; assumption).
    apply Inv_add; auto; [ apply Inv_add; auto |].
    rewrite par_add, (proj2 (Nat.eqb_neq ry rx)); auto.
  Qed.

  Lemma same_fun_inv s x y : Inv s -> x < n -> y < n -> Inv (snd (same_fun n s x y)).
  Proof.
    intros Hinv Hx Hy. unfold same_fun.
    destruct (find_fun_inv s x Hinv Hx) as (_ & _ & Hinv1 & _).
    destruct (find_fun n s x) as [rx s1].
    destruct (find_fun_inv s1 y Hinv1 Hy) as (_ & _ & Hinv2 & _).
    destruct (find_fun n s1 y) as [ry s2]. exact Hinv2.
  Qed.

End Pure.

Definition op_ok (n : nat) (o : op) : Prop :=
  match o with
  | Union x y | Same x y => x < n /\ y < n
  end.

Section Simulation.

  Context (n base : nat).

  Let arr : @STArray model_refs node := MkArrLoc base n.

  (** The array cell of every element holds its node in the map. *)
  Definition rep (m : store) (s : uf) : Prop :=
    forall i, i < n -> cell m (base + i) = Some (get s i).

  Lemma rep_add m s x nd : rep m s -> x < n ->
    rep (store_add (base + x) nd m) (NatMap.add x nd s).
  Proof.
    intros Hrep Hx i Hi. rewrite get_add. destruct (Nat.eqb_spec x i).
    - subst i. apply st_get_put_eq.
    - rewrite st_get_put_ne by lia. auto.
  Qed.

  Lemma st_spec_read m s x (Q : store -> node -> Prop) :
    rep m s -> x < n -> Q m (get s x) ->
    st_spec (E := exceptE Err) (readArray arr x) m Q.
  Proof.
    intros Hrep Hx HQ. eapply st_spec_readArray; [ exact Hx | | exact HQ ]. auto.
  Qed.

  Lemma st_spec_write m s x nd (Q : store -> unit -> Prop) :
    rep m s -> x < n -> (forall m', rep m' (NatMap.add x nd s) -> Q m' tt) ->
    st_spec (E := exceptE Err) (writeArray arr x nd) m Q.
  Proof.
    intros Hrep Hx HQ. apply st_spec_writeArray; [ exact Hx |].
    apply HQ. apply rep_add; assumption.
  Qed.

  Lemma find_sim f : forall s m x, rep m s -> Closed n s -> x < n ->
    st_spec (E := exceptE Err) (find_ST arr f x) m
      (fun m' r => r = fst (find_fun f s x) /\ rep m' (snd (find_fun f s x))).
  Proof.
    induction f as [|f IH]; intros s m x Hrep Hs Hx; cbn [find_ST find_fun].
    - apply st_spec_ret. auto.
    - apply st_spec_bind. eapply st_spec_read; [ eassumption | exact Hx |].
      pose proof (Hs x Hx) as Hp. unfold par in Hp.
      destruct (get s x) as [p k]. cbn in Hp |- *. destruct (p =? x).
      + apply st_spec_ret. auto.
      + apply st_spec_bind. eapply st_spec_weaken; [| apply IH; eassumption ].
        intros m' r [-> Hrep']. destruct (find_fun f s p) as [r s'']. cbn in *.
        apply st_spec_bind. eapply st_spec_write; [ eassumption | exact Hx |].
        intros m'' Hrep''. apply st_spec_ret. auto.
  Qed.

  Lemma union_sim s m x y : rep m s -> Closed n s -> x < n -> y < n ->
    st_spec (E := exceptE Err) (union_ST n arr x y) m (fun m' _ => rep m' (union_fun n s x y)).
  Proof.
    intros Hrep Hs Hx Hy. unfold union_ST, union_fun.
    apply st_spec_bind. eapply st_spec_weaken; [| apply find_sim; eassumption ].
    intros m1 r1 [-> Hrep1].
    destruct (find_fun_closed n n s x Hs Hx) as [Hrx Hs1].
    destruct (find_fun n s x) as [rx s1]. cbn [fst snd] in *.
    apply st_spec_bind. eapply st_spec_weaken; [| apply find_sim; eassumption ].
    intros m2 r2 [-> Hrep2].
    destruct (find_fun_closed n n s1 y Hs1 Hy) as [Hry Hs2].
    destruct (find_fun n s1 y) as [ry s2]. cbn [fst snd] in *.
    destruct (rx =? ry); [ apply st_spec_ret; exact Hrep2 |].
    apply st_spec_bind. eapply st_spec_read; [ eassumption | exact Hrx |].
    destruct (get s2 rx) as [px kx]. cbn beta iota.
    apply st_spec_bind. eapply st_spec_read; [ eassumption | exact Hry |].
    destruct (get s2 ry) as [py ky]. cbn beta iota.
    destruct (kx <? ky); [| destruct (ky <? kx)].
    - eapply st_spec_write; eauto.
    - eapply st_spec_write; eauto.
    - apply st_spec_bind. eapply st_spec_write; [ eassumption | exact Hry |].
      intros m3 Hrep3. eapply st_spec_write; eauto.
  Qed.

  Lemma same_sim s m x y : rep m s -> Closed n s -> x < n -> y < n ->
    st_spec (E := exceptE Err) (same_ST n arr x y) m
      (fun m' b => b = fst (same_fun n s x y) /\ rep m' (snd (same_fun n s x y))).
  Proof.
    intros Hrep Hs Hx Hy. unfold same_ST, same_fun.
    apply st_spec_bind. eapply st_spec_weaken; [| apply find_sim; eassumption ].
    intros m1 r1 [-> Hrep1].
    destruct (find_fun_closed n n s x Hs Hx) as [_ Hs1].
    destruct (find_fun n s x) as [rx s1]. cbn [fst snd] in *.
    apply st_spec_bind. eapply st_spec_weaken; [| apply find_sim; eassumption ].
    intros m2 r2 [-> Hrep2].
    destruct (find_fun n s1 y) as [ry s2]. apply st_spec_ret. auto.
  Qed.

  Lemma run_sim ops : forall s m, rep m s -> Closed n s -> Forall (op_ok n) ops ->
    st_spec (E := exceptE Err) (run_ST n arr ops) m (fun _ bs => bs = run_fun n s ops).
  Proof.
    induction ops as [|[x y | x y] ops IH]; intros s m Hrep Hs Hok; cbn [run_ST run_fun].
    - apply st_spec_ret. reflexivity.
    - apply Forall_cons_iff in Hok as [[Hx Hy] Hok'].
      apply st_spec_bind. eapply st_spec_weaken; [| apply union_sim; eassumption ].
      intros m' u Hrep'. apply IH; auto. apply union_fun_closed; assumption.
    - apply Forall_cons_iff in Hok as [[Hx Hy] Hok'].
      apply st_spec_bind. eapply st_spec_weaken; [| apply same_sim; eassumption ].
      intros m' b [-> Hrep'].
      pose proof (same_fun_closed n s x y Hs Hx Hy) as Hs'.
      destruct (same_fun n s x y) as [b s']. cbn in *.
      apply st_spec_bind. eapply st_spec_weaken; [| apply IH; eassumption ].
      intros m'' bs ->. apply st_spec_ret. reflexivity.
  Qed.

End Simulation.

Lemma make_sim n m :
  st_spec (E := exceptE Err) (make_ST (R := model_refs) n) m
    (fun m' a => exists base, a = MkArrLoc base n /\ rep n base m' empty_uf).
Proof.
  unfold make_ST. apply st_spec_bind, st_spec_newArray. intros base m1 _.
  apply st_spec_bind.
  eapply st_spec_weaken; [| apply (st_spec_for_each_with
    (fun rest _ m => (forall j, In j rest -> j < n)
                     /\ forall i, i < n -> ~ In i rest -> cell m (base + i) = Some (i, 0)))].
  - intros m2 _ [_ Hcells]. apply st_spec_ret. exists base. split; [ reflexivity |].
    intros i Hi. apply Hcells; auto.
  - intros x xs _ m2 [Hin Hcells]. apply st_spec_writeArray; [ apply Hin; left; reflexivity |].
    split; [ intros j Hj; apply Hin; right; exact Hj |].
    intros i Hi Hni. destruct (Nat.eq_dec x i) as [<- | Hne].
    + apply st_get_put_eq.
    + rewrite st_get_put_ne by lia.
      apply Hcells; [ exact Hi |]. intros [|]; contradiction.
  - split; [ intros j Hj; apply in_seq in Hj; lia |].
    intros i Hi Hni. exfalso. apply Hni, in_seq. lia.
Qed.

(** The imperative union-find computes the pure one. *)
Theorem union_find_fun_eq_union_find_ST : forall (n : nat) (ops : list op),
    Forall (op_ok n) ops ->
    Ret (union_find_fun n ops) ≈ runST (fun R => union_find_ST (R := R) n ops).
Proof.
  intros n ops Hok.
  destruct (st_spec_runST (fun R => union_find_ST (R := R) n ops)
              (fun bs => bs = union_find_fun n ops)) as (bs & Hrun & ->).
  - unfold union_find_ST. apply st_spec_bind.
    eapply st_spec_weaken; [| apply make_sim ].
    intros m a (base & -> & Hrep). apply run_sim; auto. intros x Hx. exact Hx.
  - symmetry. exact Hrun.
Qed.

(** Both versions on a small batch, by evaluation in the functional model. *)
Example union_find_small :
  let ops := [Union 0 1; Union 2 3; Same 0 1; Same 1 2; Union 1 3; Same 0 2; Same 3 4] in
  union_find_fun 5 ops = [true; false; true; false]
  /\ burn 200 (runST (fun R => union_find_ST (R := R) 5 ops)) = Ret [true; false; true; false].
Proof. split; lazy; reflexivity. Qed.
