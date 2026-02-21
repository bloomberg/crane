(* Bridge between a loop-structured DP model and the intrinsic Levenshtein model. *)
From Stdlib Require Import String Ascii Nat Lia List.
Import ListNotations.

Require Import Levenshtein.

Open Scope nat_scope.
Local Open Scope list_scope.

Definition dp_min (result distance bDistance : nat) : nat :=
  if Nat.ltb result distance then
    if Nat.ltb result bDistance then S result else bDistance
  else
    if Nat.ltb distance bDistance then S distance else bDistance.

Fixpoint inner_loop (a_chars : list ascii) (b_char : ascii) (old_cache : list nat)
    (distance result : nat) : list nat * nat * nat :=
  match a_chars, old_cache with
  | a_i :: a_rest, c_i :: c_rest =>
      let bDistance := if ascii_dec b_char a_i then distance else S distance in
      let new_result := dp_min result c_i bDistance in
      let '(rest_cache, fd, fr) :=
          inner_loop a_rest b_char c_rest c_i new_result in
      (new_result :: rest_cache, fd, fr)
  | _, _ => ([], distance, result)
  end.

Definition process_row (a_chars : list ascii) (b_char : ascii)
    (old_cache : list nat) (bIndex : nat) : list nat * nat :=
  let '(new_cache, _, final_result) :=
      inner_loop a_chars b_char old_cache bIndex bIndex in
  (new_cache, final_result).

Fixpoint outer_cache (a_chars b_chars : list ascii) (init : list nat)
    (k : nat) : list nat :=
  match k with
  | O => init
  | S k' =>
      let prev := outer_cache a_chars b_chars init k' in
      let b_j := nth k' b_chars Ascii.zero in
      fst (process_row a_chars b_j prev k')
  end.

Definition outer_result (a_chars b_chars : list ascii) (init : list nat)
    (k : nat) : nat :=
  match k with
  | O => 0
  | S k' =>
      let prev := outer_cache a_chars b_chars init k' in
      let b_j := nth k' b_chars Ascii.zero in
      snd (process_row a_chars b_j prev k')
  end.

Fixpoint outer_result_run (a_chars b_chars : list ascii)
    (cache : list nat) (bIndex : nat) : nat :=
  match b_chars with
  | [] => 0
  | ch :: bs =>
      let '(cache', row_res) := process_row a_chars ch cache bIndex in
      match bs with
      | [] => row_res
      | _ :: _ => outer_result_run a_chars bs cache' (S bIndex)
      end
  end.

Definition init_cache (la : nat) : list nat :=
  map S (seq 0 la).

Definition lev_dp_list (a_chars b_chars : list ascii) : nat :=
  let la := length a_chars in
  let lb := length b_chars in
  if la =? 0 then lb
  else if lb =? 0 then la
  else outer_result_run a_chars b_chars (init_cache la) 0.

Definition lev_dp_string (s t : string) : nat :=
  lev_dp_list (list_ascii_of_string s) (list_ascii_of_string t).

Lemma list_ascii_of_string_length :
  forall s, length (list_ascii_of_string s) = String.length s.
Proof.
  intros s.
  induction s as [|a s' IH]; cbn; [reflexivity |].
  now rewrite IH.
Qed.

Lemma levenshtein_computed_nil_l :
  forall t, levenshtein_computed EmptyString t = String.length t.
Proof.
  intros t.
  unfold levenshtein_computed.
  destruct t as [|a t']; cbn; reflexivity.
Qed.

Lemma levenshtein_computed_nil_r :
  forall s, levenshtein_computed s EmptyString = String.length s.
Proof.
  intros s.
  unfold levenshtein_computed.
  destruct s as [|a s']; cbn; reflexivity.
Qed.

Lemma min3_app_value_local :
  forall {t : Type} (u v w : t) (f : t -> nat),
    f (min3_app u v w f) = Nat.min (f u) (Nat.min (f v) (f w)).
Proof.
  intros t0 u v w f.
  unfold min3_app.
  destruct (Nat.leb (f u) (f v)) eqn:Huv.
  - destruct (Nat.leb (f u) (f w)) eqn:Huw.
    + apply PeanoNat.Nat.leb_le in Huv.
      apply PeanoNat.Nat.leb_le in Huw.
      rewrite (PeanoNat.Nat.min_l (f u) (Nat.min (f v) (f w))).
      2:{ apply PeanoNat.Nat.min_glb; lia. }
      reflexivity.
    + apply PeanoNat.Nat.leb_le in Huv.
      apply PeanoNat.Nat.leb_gt in Huw.
      rewrite (PeanoNat.Nat.min_r (f v) (f w)) by lia.
      rewrite (PeanoNat.Nat.min_r (f u) (f w)) by lia.
      reflexivity.
  - destruct (Nat.leb (f v) (f w)) eqn:Hvw.
    + apply PeanoNat.Nat.leb_gt in Huv.
      apply PeanoNat.Nat.leb_le in Hvw.
      rewrite (PeanoNat.Nat.min_l (f v) (f w)) by lia.
      rewrite (PeanoNat.Nat.min_r (f u) (f v)) by lia.
      reflexivity.
    + apply PeanoNat.Nat.leb_gt in Huv.
      apply PeanoNat.Nat.leb_gt in Hvw.
      rewrite (PeanoNat.Nat.min_r (f v) (f w)) by lia.
      rewrite (PeanoNat.Nat.min_r (f u) (f w)) by lia.
      reflexivity.
Qed.

Lemma min3_app_projT1_value :
  forall s t
         (u v w : {n : nat & chain s t n}),
    projT1 (min3_app u v w (fun p => projT1 p)) =
    Nat.min (projT1 u) (Nat.min (projT1 v) (projT1 w)).
Proof.
  intros s t u v w.
  exact (min3_app_value_local u v w (fun p => projT1 p)).
Qed.

Lemma levenshtein_computed_cons_neq :
  forall x xs y ys,
    x <> y ->
    levenshtein_computed (String x xs) (String y ys) =
      Nat.min (S (levenshtein_computed (String x xs) ys))
              (Nat.min (S (levenshtein_computed xs (String y ys)))
                       (S (levenshtein_computed xs ys))).
Proof.
  intros x xs y ys Hxy.
  unfold levenshtein_computed.
  cbn.
  destruct (ascii_dec x y) as [Heq|Hneq].
  { exfalso. apply Hxy. exact Heq. }
  remember (levenshtein_chain (String x xs) ys) as p1.
  remember (levenshtein_chain xs (String y ys)) as p2.
  remember (levenshtein_chain xs ys) as p3.
  destruct p1 as [n1 c1], p2 as [n2 c2], p3 as [n3 c3].
  cbn.
  try match goal with
  | |- context [let (_, _) := ?p in _] =>
      change p with (levenshtein_chain (String x xs) ys)
  end.
  try rewrite <- Heqp1.
  cbn.
  try match goal with
  | |- context [let (_, _) := ?p in _] =>
      change p with (levenshtein_chain xs (String y ys))
  end.
  try rewrite <- Heqp2.
  cbn.
  try match goal with
  | |- context [let (_, _) := ?p in _] =>
      change p with (levenshtein_chain xs ys)
  end.
  try rewrite <- Heqp3.
  cbn.
  rewrite (min3_app_projT1_value (String x xs) (String y ys)
    (existT (fun n : nat => chain (String x xs) (String y ys) n) (S n1)
            (insert_chain y (String x xs) ys n1 c1))
    (existT (fun n : nat => chain (String x xs) (String y ys) n) (S n2)
            (delete_chain x xs (String y ys) n2 c2))
    (existT (fun n : nat => chain (String x xs) (String y ys) n) (S n3)
            (update_chain x y xs ys n3 Hneq c3))).
  pose proof
    (levenshtein_computed_of_chain (String x xs) ys n1 c1 (eq_sym Heqp1))
    as Hp1.
  pose proof
    (levenshtein_computed_of_chain xs (String y ys) n2 c2 (eq_sym Heqp2))
    as Hp2.
  pose proof
    (levenshtein_computed_of_chain xs ys n3 c3 (eq_sym Heqp3))
    as Hp3.
  cbn.
  reflexivity.
Qed.

Definition lev_spec_list (a b : list ascii) : nat :=
  levenshtein_computed (string_of_list_ascii a) (string_of_list_ascii b).

Lemma string_of_list_ascii_length :
  forall l, String.length (string_of_list_ascii l) = length l.
Proof.
  intros l.
  induction l as [|a l IH]; cbn; [reflexivity|].
  now rewrite IH.
Qed.

Lemma lev_spec_list_nil_l :
  forall b, lev_spec_list [] b = length b.
Proof.
  intros b.
  unfold lev_spec_list.
  rewrite levenshtein_computed_nil_l.
  rewrite string_of_list_ascii_length.
  reflexivity.
Qed.

Lemma lev_spec_list_nil_r :
  forall a, lev_spec_list a [] = length a.
Proof.
  intros a.
  unfold lev_spec_list.
  rewrite levenshtein_computed_nil_r.
  rewrite string_of_list_ascii_length.
  reflexivity.
Qed.

Lemma lev_spec_list_cons_eq :
  forall x xs ys,
    lev_spec_list (x :: xs) (x :: ys) = lev_spec_list xs ys.
Proof.
  intros x xs ys.
  unfold lev_spec_list.
  cbn.
  apply levenshtein_computed_skip_eq.
Qed.

Lemma lev_spec_list_cons_neq :
  forall x xs y ys,
    x <> y ->
    lev_spec_list (x :: xs) (y :: ys) =
      Nat.min (S (lev_spec_list (x :: xs) ys))
              (Nat.min (S (lev_spec_list xs (y :: ys)))
                       (S (lev_spec_list xs ys))).
Proof.
  intros x xs y ys Hxy.
  unfold lev_spec_list.
  cbn.
  apply levenshtein_computed_cons_neq.
  exact Hxy.
Qed.

Lemma dp_min_spec : forall r d bd,
  dp_min r d bd = Nat.min (S r) (Nat.min (S d) bd).
Proof.
  intros r d bd.
  unfold dp_min.
  destruct (Nat.ltb r d) eqn:Hrd.
  - destruct (Nat.ltb r bd) eqn:Hrb.
    + apply PeanoNat.Nat.ltb_lt in Hrd.
      apply PeanoNat.Nat.ltb_lt in Hrb.
      rewrite (PeanoNat.Nat.min_l (S r) (Nat.min (S d) bd)).
      2:{
        apply PeanoNat.Nat.min_glb.
        lia.
        apply PeanoNat.Nat.le_trans with (m := S r); lia.
      }
      reflexivity.
    + apply PeanoNat.Nat.ltb_lt in Hrd.
      apply PeanoNat.Nat.ltb_ge in Hrb.
      rewrite (PeanoNat.Nat.min_r (S d) bd) by lia.
      rewrite (PeanoNat.Nat.min_r (S r) bd) by lia.
      reflexivity.
  - destruct (Nat.ltb d bd) eqn:Hdb.
    + apply PeanoNat.Nat.ltb_ge in Hrd.
      apply PeanoNat.Nat.ltb_lt in Hdb.
      rewrite (PeanoNat.Nat.min_l (S d) bd) by lia.
      rewrite (PeanoNat.Nat.min_r (S r) (S d)) by lia.
      reflexivity.
    + apply PeanoNat.Nat.ltb_ge in Hrd.
      apply PeanoNat.Nat.ltb_ge in Hdb.
      rewrite (PeanoNat.Nat.min_r (S d) bd) by lia.
      rewrite (PeanoNat.Nat.min_r (S r) bd) by lia.
      reflexivity.
Qed.

Lemma lev_dp_list_nil_l : forall b,
  lev_dp_list [] b = length b.
Proof.
  intros b.
  unfold lev_dp_list.
  simpl.
  reflexivity.
Qed.

Lemma lev_dp_list_nil_r : forall a,
  lev_dp_list a [] = length a.
Proof.
  intros a.
  unfold lev_dp_list.
  destruct a; simpl; reflexivity.
Qed.

Lemma lev_dp_string_nil_l_eq :
  forall t, lev_dp_string EmptyString t = levenshtein_computed EmptyString t.
Proof.
  intros t.
  unfold lev_dp_string.
  rewrite lev_dp_list_nil_l.
  rewrite list_ascii_of_string_length.
  rewrite levenshtein_computed_nil_l.
  reflexivity.
Qed.

Lemma lev_dp_string_nil_r_eq :
  forall s, lev_dp_string s EmptyString = levenshtein_computed s EmptyString.
Proof.
  intros s.
  unfold lev_dp_string.
  rewrite lev_dp_list_nil_r.
  rewrite list_ascii_of_string_length.
  rewrite levenshtein_computed_nil_r.
  reflexivity.
Qed.

(* Row specification where [pre_rev] is the reverse of the already-processed
   prefix of [a], and [brow] is the reverse of the current [b]-prefix. *)
Fixpoint row_values (pre_rev a_rest brow : list ascii) : list nat :=
  match a_rest with
  | [] => []
  | a_i :: a_tail =>
      lev_spec_list (a_i :: pre_rev) brow
      :: row_values (a_i :: pre_rev) a_tail brow
  end.

Fixpoint row_last (pre_rev a_rest brow : list ascii) : nat :=
  match a_rest with
  | [] => lev_spec_list pre_rev brow
  | a_i :: a_tail => row_last (a_i :: pre_rev) a_tail brow
  end.

Lemma row_values_nil :
  forall pre_rev a_rest,
    row_values pre_rev a_rest [] =
    map S (seq (length pre_rev) (length a_rest)).
Proof.
  intros pre_rev a_rest.
  revert pre_rev.
  induction a_rest as [|a_i a_tail IH]; intros pre_rev; cbn [row_values].
  - reflexivity.
  - rewrite lev_spec_list_nil_r.
    rewrite IH.
    reflexivity.
Qed.

Lemma init_cache_row_values :
  forall a_rest, init_cache (length a_rest) = row_values [] a_rest [].
Proof.
  intros a_rest.
  unfold init_cache.
  rewrite row_values_nil.
  reflexivity.
Qed.

Lemma lev_spec_list_insert_lower_l :
  forall a s t,
    lev_spec_list s t <= S (lev_spec_list (a :: s) t).
Proof.
  intros a s t.
  unfold lev_spec_list.
  apply levenshtein_computed_insert_lower.
Qed.

Lemma lev_spec_list_insert_lower_r :
  forall a s t,
    lev_spec_list s t <= S (lev_spec_list s (a :: t)).
Proof.
  intros a s t.
  unfold lev_spec_list.
  apply levenshtein_computed_insert_lower_r.
Qed.

Lemma dp_cell_eq_cont :
  forall x pre_rev bpre_rev,
    dp_min (lev_spec_list pre_rev (x :: bpre_rev))
           (lev_spec_list (x :: pre_rev) bpre_rev)
           (lev_spec_list pre_rev bpre_rev)
    = lev_spec_list (x :: pre_rev) (x :: bpre_rev).
Proof.
  intros x pre_rev bpre_rev.
  rewrite dp_min_spec.
  rewrite lev_spec_list_cons_eq.
  rewrite (PeanoNat.Nat.min_r
             (S (lev_spec_list (x :: pre_rev) bpre_rev))
             (lev_spec_list pre_rev bpre_rev)).
  2:{ apply lev_spec_list_insert_lower_l. }
  rewrite (PeanoNat.Nat.min_r
             (S (lev_spec_list pre_rev (x :: bpre_rev)))
             (lev_spec_list pre_rev bpre_rev)).
  2:{ apply lev_spec_list_insert_lower_r. }
  reflexivity.
Qed.

Lemma dp_cell_neq_cont :
  forall x y pre_rev bpre_rev,
    x <> y ->
    dp_min (lev_spec_list pre_rev (y :: bpre_rev))
           (lev_spec_list (x :: pre_rev) bpre_rev)
           (S (lev_spec_list pre_rev bpre_rev))
    = lev_spec_list (x :: pre_rev) (y :: bpre_rev).
Proof.
  intros x y pre_rev bpre_rev Hxy.
  rewrite dp_min_spec.
  rewrite lev_spec_list_cons_neq by exact Hxy.
  rewrite min3_comm12.
  reflexivity.
Qed.

Lemma dp_cell_first_eq :
  forall x bpre_rev,
    dp_min (lev_spec_list [] bpre_rev)
           (lev_spec_list [x] bpre_rev)
           (lev_spec_list [] bpre_rev)
    = lev_spec_list [x] (x :: bpre_rev).
Proof.
  intros x bpre_rev.
  rewrite dp_min_spec.
  rewrite lev_spec_list_cons_eq.
  rewrite PeanoNat.Nat.min_r by lia.
  rewrite PeanoNat.Nat.min_r.
  2:{
    specialize (lev_spec_list_insert_lower_l x [] bpre_rev) as H.
    simpl in H.
    exact H.
  }
  reflexivity.
Qed.

Lemma dp_cell_first_neq :
  forall x y bpre_rev,
    x <> y ->
    dp_min (lev_spec_list [] bpre_rev)
           (lev_spec_list [x] bpre_rev)
           (S (lev_spec_list [] bpre_rev))
    = lev_spec_list [x] (y :: bpre_rev).
Proof.
  intros x y bpre_rev Hxy.
  set (d := lev_spec_list [] bpre_rev).
  set (c := lev_spec_list [x] bpre_rev).
  rewrite dp_min_spec.
  rewrite lev_spec_list_cons_neq by exact Hxy.
  assert (Hd : lev_spec_list [] (y :: bpre_rev) = S d).
  {
    unfold d.
    rewrite !lev_spec_list_nil_l.
    simpl.
    lia.
  }
  rewrite Hd.
  fold c d.
  rewrite min3_comm12.
  rewrite PeanoNat.Nat.min_id.
  replace (Nat.min (S (S d)) (S d)) with (S d).
  2:{ symmetry. apply PeanoNat.Nat.min_r. lia. }
  reflexivity.
Qed.

Lemma inner_loop_cont_correct :
  forall pre_rev a_rest b_char bpre_rev,
    inner_loop a_rest b_char (row_values pre_rev a_rest bpre_rev)
      (lev_spec_list pre_rev bpre_rev)
      (lev_spec_list pre_rev (b_char :: bpre_rev))
    =
    (row_values pre_rev a_rest (b_char :: bpre_rev),
     row_last pre_rev a_rest bpre_rev,
     row_last pre_rev a_rest (b_char :: bpre_rev)).
Proof.
  intros pre_rev a_rest.
  revert pre_rev.
  induction a_rest as [|a_i a_tail IH]; intros pre_rev b_char bpre_rev; cbn.
  - reflexivity.
  - destruct (ascii_dec b_char a_i) as [Heq|Hneq].
    + subst a_i.
      rewrite dp_cell_eq_cont.
      rewrite (IH (b_char :: pre_rev) b_char bpre_rev).
      reflexivity.
    + rewrite dp_cell_neq_cont.
      2:{ intro Hc. apply Hneq. symmetry. exact Hc. }
      rewrite (IH (a_i :: pre_rev) b_char bpre_rev).
      reflexivity.
Qed.

Lemma process_row_correct_nonempty :
  forall a0 a_tail b_char bpre_rev,
    process_row (a0 :: a_tail) b_char
      (row_values [] (a0 :: a_tail) bpre_rev)
      (length bpre_rev)
    =
    (row_values [] (a0 :: a_tail) (b_char :: bpre_rev),
     row_last [] (a0 :: a_tail) (b_char :: bpre_rev)).
Proof.
  intros a0 a_tail b_char bpre_rev.
  unfold process_row.
  cbn [row_values].
  replace (length bpre_rev) with (lev_spec_list [] bpre_rev).
  2:{ exact (lev_spec_list_nil_l bpre_rev). }
  destruct (ascii_dec b_char a0) as [Heq|Hneq].
  - subst a0.
    cbn.
    destruct (ascii_dec b_char b_char) as [Hbb|Hbb].
    2:{ exfalso. apply Hbb. reflexivity. }
    rewrite dp_cell_first_eq.
    rewrite inner_loop_cont_correct with
      (pre_rev := [b_char]) (a_rest := a_tail)
      (b_char := b_char) (bpre_rev := bpre_rev).
    reflexivity.
  - remember (if ascii_dec b_char a0
              then lev_spec_list [] bpre_rev
              else S (lev_spec_list [] bpre_rev)) as bd0 eqn:Hbd0.
    assert (Hbd0' : bd0 = S (lev_spec_list [] bpre_rev)).
    {
      rewrite Hbd0.
      destruct (ascii_dec b_char a0) as [Hc|Hc].
      - exfalso. apply Hneq. exact Hc.
      - reflexivity.
    }
    rewrite Hbd0' in *.
    cbn [inner_loop].
    destruct (ascii_dec b_char a0) as [Hc|Hc].
    + exfalso. apply Hneq. exact Hc.
    + cbn.
    rewrite (dp_cell_first_neq a0 b_char bpre_rev).
    2:{ intro Heq'. apply Hneq. symmetry. exact Heq'. }
    rewrite inner_loop_cont_correct with
      (pre_rev := [a0]) (a_rest := a_tail)
      (b_char := b_char) (bpre_rev := bpre_rev).
    reflexivity.
Qed.

Lemma row_last_rev :
  forall pre_rev a_rest brow,
    row_last pre_rev a_rest brow =
    lev_spec_list (rev a_rest ++ pre_rev) brow.
Proof.
  intros pre_rev a_rest brow.
  revert pre_rev.
  induction a_rest as [|a_i a_tail IH]; intros pre_rev; cbn.
  - reflexivity.
  - rewrite (IH (a_i :: pre_rev)).
    cbn [rev].
    change (a_i :: pre_rev) with ([a_i] ++ pre_rev).
    rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma outer_result_run_correct :
  forall a b bpre_rev,
    a <> [] ->
    b <> [] ->
    outer_result_run a b (row_values [] a bpre_rev) (length bpre_rev)
    = row_last [] a (rev b ++ bpre_rev).
Proof.
  intros a b bpre_rev Ha Hb.
  revert bpre_rev Hb.
  induction b as [|b0 b_tail IH]; intros bpre_rev Hb; [contradiction|].
  destruct a as [|a0 a_tail]; [contradiction|].
  cbn [outer_result_run].
  rewrite process_row_correct_nonempty.
  destruct b_tail as [|b1 b_tail'].
  - cbn.
    reflexivity.
  - 
    specialize (IH (b0 :: bpre_rev) ltac:(discriminate)).
    replace (S (length bpre_rev)) with (length (b0 :: bpre_rev)) by reflexivity.
    rewrite IH.
    cbn [rev].
    change (b0 :: bpre_rev) with ([b0] ++ bpre_rev).
    repeat rewrite <- app_assoc.
    reflexivity.
Qed.

Theorem lev_dp_list_rev_spec :
  forall a b,
    lev_dp_list a b = lev_spec_list (rev a) (rev b).
Proof.
  intros a b.
  destruct a as [|a0 a_tail].
  - rewrite lev_dp_list_nil_l.
    rewrite lev_spec_list_nil_l.
    rewrite length_rev.
    reflexivity.
  - destruct b as [|b0 b_tail].
    + rewrite lev_dp_list_nil_r.
      rewrite lev_spec_list_nil_r.
      rewrite length_rev.
      reflexivity.
    + unfold lev_dp_list.
      cbn [length Nat.eqb].
      change (init_cache (S (length a_tail)))
        with (init_cache (length (a0 :: a_tail))).
      rewrite init_cache_row_values.
      rewrite outer_result_run_correct by discriminate.
      rewrite row_last_rev with (pre_rev := []).
      cbn.
      repeat rewrite app_nil_r.
      reflexivity.
Qed.

Lemma lev_dp_string_rev_spec :
  forall s t,
    lev_dp_string s t =
    lev_spec_list (rev (list_ascii_of_string s))
                  (rev (list_ascii_of_string t)).
Proof.
  intros s t.
  unfold lev_dp_string.
  apply lev_dp_list_rev_spec.
Qed.

Lemma chain_append_right :
  forall s t n (c : chain s t n) u,
    chain (s ++ u) (t ++ u) n.
Proof.
  intros s t n c.
  induction c as [|a s1 t1 n1 c1 IH|s1 t1 u1 n1 e c1 IH]; intros u.
  - exact (same_chain u).
  - cbn [String.append].
    apply skip.
    exact (IH u).
  - destruct e.
    + cbn [String.append].
      eapply change.
      * exact (insertion a).
      * exact (IH u).
    + cbn [String.append].
      eapply change.
      * exact (deletion a).
      * exact (IH u).
    + cbn [String.append].
      eapply change.
      * exact (update a' a (neq := neq)).
      * exact (IH u).
Qed.

Lemma chain_add_last_source :
  forall s t n (c : chain s t n) a,
    chain (s ++ String a EmptyString) t (S n).
Proof.
  intros s t n c.
  induction c as [|x s1 t1 n1 c1 IH|s1 t1 u1 n1 e c1 IH]; intros a.
  - cbn [String.append].
    exact (delete_chain a EmptyString EmptyString 0 empty).
  - cbn [String.append].
    apply skip.
    exact (IH a).
  - destruct e.
    + cbn [String.append].
      eapply change.
      * exact (insertion a0).
      * exact (IH a).
    + cbn [String.append].
      eapply change.
      * exact (deletion a0).
      * exact (IH a).
    + cbn [String.append].
      eapply change.
      * exact (update a' a0 (neq := neq)).
      * exact (IH a).
Qed.

Lemma chain_strip_last_source :
  forall s a t n,
    chain (s ++ String a EmptyString) t n ->
    chain s t (S n).
Proof.
  intros s a t n c.
  remember (String.append s (String a EmptyString)) as src eqn:Hsrc.
  revert s a Hsrc.
  induction c as [|x s1 t1 n1 c1 IH|s1 t1 u1 n1 e c1 IH];
    intros s0 a0 Hsrc.
  - destruct s0; cbn in Hsrc; discriminate.
  - destruct s0 as [|y s0']; cbn in Hsrc.
    + inversion Hsrc; subst.
      eapply change.
      * constructor.
      * apply skip.
        exact c1.
    + inversion Hsrc; subst.
      apply skip.
      apply IH with (a := a0).
      reflexivity.
  - destruct e as [ch s2|ch s2|ch' ch Hneq s2].
    + eapply change.
      * constructor.
      * apply IH with (s := String ch s0) (a := a0).
        cbn [String.append].
        now rewrite Hsrc.
    + destruct s0 as [|y s0']; cbn in Hsrc.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (insertion a0).
        -- eapply change.
           ++ exact (deletion a0).
           ++ exact c1.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (deletion y).
        -- apply IH with (s := s0') (a := a0).
           reflexivity.
    + destruct s0 as [|y s0']; cbn in Hsrc.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (insertion a0).
        -- eapply change.
           ++ exact (update a0 ch (neq := Hneq)).
           ++ exact c1.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (update y ch (neq := Hneq)).
        -- apply IH with (s := String ch s0') (a := a0).
           cbn [String.append].
           reflexivity.
Qed.

Lemma chain_update_last_source :
  forall s a a' t n,
    a' <> a ->
    chain (s ++ String a EmptyString) t n ->
    chain (s ++ String a' EmptyString) t (S n).
Proof.
  intros s a a' t n Hneq_sa c.
  remember (String.append s (String a EmptyString)) as src eqn:Hsrc.
  revert s a Hneq_sa Hsrc.
  induction c as [|x s1 t1 n1 c1 IH|s1 t1 u1 n1 e c1 IH];
    intros s0 a0 Hneq0 Hsrc.
  - destruct s0; cbn in Hsrc; discriminate.
  - destruct s0 as [|y s0']; cbn in Hsrc.
    + inversion Hsrc; subst.
      eapply change.
      * exact (update a' a0 (neq := Hneq0)).
      * apply skip.
        exact c1.
    + inversion Hsrc; subst.
      apply skip.
      apply IH with (a := a0).
      * exact Hneq0.
      * reflexivity.
  - destruct e as [ch s2|ch s2|ch' ch Hneq_e s2].
    + eapply change.
      * exact (insertion ch).
      * apply IH with (s := String ch s0) (a := a0).
        -- exact Hneq0.
        -- cbn [String.append].
           now rewrite Hsrc.
    + destruct s0 as [|y s0']; cbn in Hsrc.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (update a' a0 (neq := Hneq0)).
        -- eapply change.
           ++ exact (deletion a0).
           ++ exact c1.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (deletion y).
        -- apply IH with (s := s0') (a := a0).
           ++ exact Hneq0.
           ++ reflexivity.
    + destruct s0 as [|y s0']; cbn in Hsrc.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (update a' a0 (neq := Hneq0)).
        -- eapply change.
           ++ exact (update a0 ch (neq := Hneq_e)).
           ++ exact c1.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (update y ch (neq := Hneq_e)).
        -- apply IH with (s := String ch s0') (a := a0).
           ++ exact Hneq0.
           ++ cbn [String.append].
              reflexivity.
Qed.

Lemma string_of_list_ascii_app :
  forall l1 l2,
    string_of_list_ascii (l1 ++ l2) =
    String.append (string_of_list_ascii l1) (string_of_list_ascii l2).
Proof.
  intros l1 l2.
  induction l1 as [|x xs IH]; cbn.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Definition rev_string (s : string) : string :=
  string_of_list_ascii (rev (list_ascii_of_string s)).

Lemma rev_string_cons :
  forall a s,
    rev_string (String a s) =
    String.append (rev_string s) (String a EmptyString).
Proof.
  intros a s.
  unfold rev_string.
  cbn [list_ascii_of_string rev].
  rewrite string_of_list_ascii_app.
  cbn [string_of_list_ascii String.append].
  reflexivity.
Qed.

Lemma rev_string_of_list :
  forall l,
    rev_string (string_of_list_ascii l) = string_of_list_ascii (rev l).
Proof.
  intros l.
  unfold rev_string.
  rewrite list_ascii_of_string_of_list_ascii.
  reflexivity.
Qed.

Lemma rev_string_involutive :
  forall s, rev_string (rev_string s) = s.
Proof.
  intros s.
  unfold rev_string.
  rewrite list_ascii_of_string_of_list_ascii.
  rewrite rev_involutive.
  rewrite string_of_list_ascii_of_string.
  reflexivity.
Qed.

Lemma chain_rev_string :
  forall s t n (c : chain s t n),
    chain (rev_string s) (rev_string t) n.
Proof.
  intros s t n c.
  induction c as [|a s1 t1 n1 c1 IH|s1 t1 u1 n1 e c1 IH].
  - unfold rev_string.
    cbn [list_ascii_of_string rev string_of_list_ascii].
    constructor.
  - rewrite !rev_string_cons.
    exact (chain_append_right _ _ _ IH (String a EmptyString)).
  - destruct e as [ch s2|ch s2|ch' ch Hneq s2].
    + rewrite rev_string_cons in IH.
      exact (chain_strip_last_source (rev_string s2) ch (rev_string u1) n1 IH).
    + rewrite rev_string_cons.
      exact (chain_add_last_source (rev_string s2) (rev_string u1) n1 IH ch).
    + rewrite rev_string_cons.
      rewrite rev_string_cons in IH.
      exact (chain_update_last_source (rev_string s2) ch ch' (rev_string u1) n1 Hneq IH).
Qed.

Lemma levenshtein_computed_rev_string :
  forall s t,
    levenshtein_computed (rev_string s) (rev_string t) =
    levenshtein_computed s t.
Proof.
  intros s t.
  apply PeanoNat.Nat.le_antisymm.
  - destruct (levenshtein_chain s t) as [n c] eqn:Hchain.
    pose proof
      (levenshtein_computed_of_chain s t n c Hchain)
      as Hn.
    pose proof
      (chain_rev_string s t n c)
      as Hrev.
    pose proof
      (levenshtein_computed_is_minimal (rev_string s) (rev_string t) n Hrev)
      as Hmin.
    rewrite <- Hn in Hmin.
    exact Hmin.
  - destruct (levenshtein_chain (rev_string s) (rev_string t)) as [n c] eqn:Hchain.
    pose proof
      (levenshtein_computed_of_chain (rev_string s) (rev_string t) n c Hchain)
      as Hn.
    pose proof
      (chain_rev_string (rev_string s) (rev_string t) n c)
      as Hrev.
    pose proof
      (levenshtein_computed_is_minimal
         (rev_string (rev_string s)) (rev_string (rev_string t)) n Hrev)
      as Hmin.
    rewrite !rev_string_involutive in Hmin.
    rewrite Hn.
    exact Hmin.
Qed.

Lemma lev_spec_list_rev :
  forall a b,
    lev_spec_list (rev a) (rev b) = lev_spec_list a b.
Proof.
  intros a b.
  unfold lev_spec_list.
  rewrite <- (rev_string_of_list a).
  rewrite <- (rev_string_of_list b).
  apply levenshtein_computed_rev_string.
Qed.

Theorem lev_dp_string_eq_levenshtein_computed :
  forall s t, lev_dp_string s t = levenshtein_computed s t.
Proof.
  intros s t.
  rewrite lev_dp_string_rev_spec.
  rewrite lev_spec_list_rev.
  unfold lev_spec_list.
  rewrite !string_of_list_ascii_of_string.
  reflexivity.
Qed.
