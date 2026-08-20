(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import Arith Lia List PeanoNat Relation_Operators.
From Crane.Libraries.ParseALot.Parser Require Import Defs.
From Crane.Libraries.ParseALot.Parser Require Import Lex.
From Crane.Libraries.ParseALot.Parser Require Import Tactics.
From Crane.Libraries.ParseALot.Parser Require Import Utils.
Import ListNotations.

Module TerminationFn (Export D : Defs.T).

  (* Definitions related to well-founded measures *)

  (** The size of the top (head) stack frame: the number of remaining symbols. *)
  Definition head_frame_size {A} (ys : list A) : nat :=
    length ys.
  
  (** Weighted score for the head frame: [|ys| * b^e], placing it at positional value [e]. *)
  Definition head_frame_score {A} (ys : list A) (b e : nat) : nat :=
    head_frame_size ys * (b ^ e).

  (** The size of a tail frame: the number of symbols still to process after the current nonterminal. *)
  Definition tail_frame_size {A} (ys : list A) : nat :=
    match ys with
    | []       => 0
    | _ :: suf => length suf
    end.
                                                  
  (** Weighted score for a single tail frame: [tail_frame_size ys * b^e]. *)
  Definition tail_frame_score {A} (ys : list A) (b e : nat) : nat :=
    tail_frame_size ys * (b ^ e).

  (** Sum of positional scores for all tail frames, with each successive frame's exponent incremented by 1. *)
  Fixpoint tail_frames_score {A} (yss : list (list A)) (b e : nat) : nat :=
    match yss with
    | []         => 0
    | ys :: yss' => tail_frame_score ys b e + tail_frames_score yss' b (1 + e)
    end.

  (** Total positional score for a stack: head frame at exponent [e], tail frames at increasing exponents. *)
  Definition stack_score {A} (stk : list A * list (list A)) (b e : nat) : nat :=
    match stk with
    | (fr, frs) => head_frame_score fr b e + tail_frames_score frs b (1 + e)
    end.

  (** The number of frames on the stack (head plus all tail frames). *)
  Definition stack_height {A} (stk : A * list A) : nat :=
    match stk with
    | (fr, frs) => List.length (fr :: frs)
    end.

  (* Termination-related lemmas *)
  
  (** Monotonicity of exponentiation: a larger (positive) exponent gives a larger power. *)
  Lemma nonzero_exponents_le__powers_le :
    forall b e1 e2,
      0 < e1 <= e2
      -> b ^ e1 <= b ^ e2.
  Proof.
    intros b e1 e2 [Hlt Hlt']. 
    destruct b as [| b']. 
    - destruct e1; destruct e2; auto; lia.
    - apply Nat.pow_le_mono_r; auto. 
  Qed.
  
  (** A single tail frame's score is monotone in the exponent when the exponent is positive. *)
  Lemma nonzero_exponents_le__tail_frame_score_le :
    forall A (fr : list A) b e1 e2,
      0 < e1 <= e2
      -> tail_frame_score fr b e1 <= tail_frame_score fr b e2.
  Proof.
    intros A fr b e1 e2 Hlt.
    unfold tail_frame_score. 
    apply Nat.mul_le_mono_l.
    apply nonzero_exponents_le__powers_le; auto.
  Qed.

  (** The combined tail-frames score is monotone in the starting exponent when the exponent is positive. *)
  Lemma nonzero_exponents_le__tail_frames_score_le :
    forall A (frs : list (list A)) b e1 e2,
      0 < e1 <= e2
      -> tail_frames_score frs b e1 <= tail_frames_score frs b e2.
  Proof.
    intros A frs.
    induction frs as [| fr frs' IH]; intros b e1 e2 Hlt; simpl; auto.
    apply Nat.add_le_mono.
    - apply nonzero_exponents_le__tail_frame_score_le; auto.
    - apply IH; lia.
  Qed.

  (** Increasing both the head-frame exponent and the tail-frames starting exponent (when positive) cannot decrease the stack score. *)
  Lemma nonzero_exponents_le__stack_score_le :
    forall A v b e1 e2 e3 e4 (frs : list (list A)),
      0 < e1 <= e2
      -> 0 < e3 <= e4
      -> v * (b ^ e1) + tail_frames_score frs b e3 <=
         v * (b ^ e2) + tail_frames_score frs b e4.
  Proof.
    intros A v b e1 e2 e3 e4 frs [H0e1 He1e2] [H0e3 He3e4].
    apply Nat.add_le_mono.
    - apply Nat.mul_le_mono_l. 
      apply nonzero_exponents_le__powers_le; auto.
    - apply nonzero_exponents_le__tail_frames_score_le; auto.
  Qed.

  (*
  Lemma nonzero_exponents_le__stack_score_le :
    forall A v b e1 e2 e3 e4 (frs : list (list A)),
      0 < e1 <= e2
      -> 0 < e3 <= e4
      -> v * (b ^ e1) + tail_frames_score frs b e3 <= 
         v * (b ^ e2) + tail_frames_score frs b e4.
  Proof.
    intros.
    
    intros ? ? ? ? ? ? ? ; intros.
    unfold stack_score.
    apply nonzero_exponents_le__tail_frames_score_le; auto.
  Qed.
   *)
  
  (** If [x] is in set [s], then [s] is non-empty (its cardinality is not zero). *)
  Lemma mem_true_cardinality_neq_0 :
    forall x s,
      NtSet.mem x s = true -> NtSet.cardinal s <> 0.
  Proof.
    intros x s Hm; unfold not; intros Heq.
    apply NF.mem_iff in Hm.
    apply cardinal_inv_1 in Heq.
    unfold NtSet.Empty in Heq. 
    eapply Heq; eauto.
  Qed.
  
  (** Membership in [s] implies the cardinality of [s] is strictly positive. *)
  Lemma mem_true_cardinality_gt_0 :
    forall x s,
      NtSet.mem x s = true -> 0 < NtSet.cardinal s.
  Proof.
    intros x s Hm.
    apply mem_true_cardinality_neq_0 in Hm; lia.
  Qed.

  (** If [x ∈ s], then [s ∖ (s' ∖ {x})] is non-empty because [x] is always present in the difference. *)
  Lemma cardinal_diff_remove_gt_0 :
    forall x s s',
      NtSet.In x s
      -> 0 < NtSet.cardinal (NtSet.diff s (NtSet.remove x s')).
  Proof.
    intros x s s' hm.
    apply mem_true_cardinality_gt_0 with (x := x).
    apply NF.mem_iff; ND.fsetdec.
  Qed.

  (** If [x ∈ s] but [x ∉ s'], then the difference [s ∖ s'] contains [x] and is non-empty. *)
  Lemma cardinal_diff_gt_0 :
    forall x s s',
      NtSet.In x s
      -> ~ NtSet.In x s'
      -> 0 < NtSet.cardinal (NtSet.diff s s').
  Proof.
    intros x s s' hi hn.
    apply mem_true_cardinality_gt_0 with (x := x).
    apply NF.mem_iff; ND.fsetdec.
  Qed.

  (** Set identity: removing [x] from the subtracted set is the same as adding [x] back to the difference. *)
  Lemma diff_remove_equal_add_diff :
    forall x s s',
      NtSet.In x s
      -> NtSet.Equal (NtSet.diff s (NtSet.remove x s'))
                     (NtSet.add x (NtSet.diff s s')).
  Proof.
    intros; ND.fsetdec.
  Qed.

  (** If [x ∉ s], removing [x] from the subtracted set does not change the difference. *)
  Lemma diff_remove_equal_diff_1 :
    forall x s s',
      ~ NtSet.In x s
      -> NtSet.Equal (NtSet.diff s (NtSet.remove x s')) (NtSet.diff s s').
  Proof.
    intros x s s' hm; ND.fsetdec.
  Qed.
  
  (** If [x ∉ s'], then [x] was not in [s'] to begin with and removing it is a no-op on the difference. *)
  Lemma diff_remove_equal_diff_2 :
    forall x s s',
      ~ NtSet.In x s'
      -> NtSet.Equal (NtSet.diff s (NtSet.remove x s')) (NtSet.diff s s').
  Proof.
    intros x s s' hm; ND.fsetdec.
  Qed.
  
  (** Removing [x] from the subtracted set increases the difference's cardinality by at most 1. *)
  Lemma cardinal_diff_remove_le :
    forall x s s',
      NtSet.In x s
      -> NtSet.In x s'
      -> NtSet.cardinal (NtSet.diff s (NtSet.remove x s')) <=
         S (NtSet.cardinal (NtSet.diff s s')).
    intros x s s' hi hm.
    rewrite diff_remove_equal_add_diff; auto.
    rewrite add_cardinal_2; auto.
    apply not_mem_iff; ND.fsetdec.
  Qed.

  (** When [x ∉ s], removing [x] from [s'] before differencing yields the same result as the plain difference. *)
  Lemma diff_remove_equal_diff :
    forall x s s',
      ~ NtSet.In x s
      -> NtSet.Equal (NtSet.diff s (NtSet.remove x s'))
                     (NtSet.diff s s').
  Proof.
    intros; ND.fsetdec.
  Qed.
  
  (** After returning from a callee with an empty suffix, the caller's stack score does not increase:
      the exponent grows by at most 1 but the visited set shrinks, keeping the score bounded. *)
  Lemma stack_score_le_after_return :
    forall callee_suf caller_suf caller_suf' x suf vi u locs b,
      callee_suf = []
      -> caller_suf = NT x :: suf
      -> caller_suf' = suf
      -> NtSet.In x u
      -> stack_score (caller_suf', locs) b (NtSet.cardinal (NtSet.diff u (NtSet.remove x vi)))
         <= stack_score (callee_suf, caller_suf :: locs) b (NtSet.cardinal (NtSet.diff u vi)).
  Proof.
    intros ce cr cr' x suf vi u locs b hce hcr hcr' hi; subst.
    unfold stack_score; simpl.
    unfold head_frame_score; unfold head_frame_size.
    unfold tail_frame_score; unfold tail_frame_size.
    destruct (NtSet.mem x vi) eqn:hm.
    - apply NF.mem_iff in hm.
      assert (hi' : NtSet.In x u) by ND.fsetdec.
      apply nonzero_exponents_le__stack_score_le; split; try lia.
      + apply cardinal_diff_remove_gt_0; auto. 
      + apply cardinal_diff_remove_le; auto.
      + apply le_n_S; apply cardinal_diff_remove_le; auto. 
    - apply not_mem_iff in hm.
      rewrite diff_remove_equal_diff_2; auto.
      apply nonzero_exponents_le__stack_score_le; split; try lia.
      eapply cardinal_diff_gt_0; eauto.
  Qed.

  (** Cleaner restated version of [stack_score_le_after_return] for direct use in termination proofs. *)
  Lemma stack_score_le_after_return' :
    forall x suf b vi u frs,
      NtSet.In x u
      -> stack_score (suf, frs)
                    b
                    (NtSet.cardinal (NtSet.diff u (NtSet.remove x vi)))
         <=
         stack_score ([], (NT x :: suf) :: frs)
                    b
                    (NtSet.cardinal (NtSet.diff u vi)).
  Proof.
    intros; eapply stack_score_le_after_return; sis; eauto.
  Qed.
  
  (** Removing a present element decreases cardinality by exactly 1. *)
  Lemma remove_cardinal_minus_1 :
    forall (x : nonterminal) (s : NtSet.t),
      NtSet.mem x s = true
      -> NtSet.cardinal (NtSet.remove x s) = NtSet.cardinal s - 1.
  Proof.
    intros x s Hm.
    rewrite <- remove_cardinal_1 with (s := s) (x := x); auto.
    lia.
  Qed.

  (** Multiplying a larger value by a positive factor preserves strict inequality: [x < y -> 0 < z -> x < y*z]. *)
  Lemma lt_lt_mul_nonzero_r :
    forall y x z,
      x < y -> 0 < z -> x < y * z.
  Proof.
    intros y x z Hxy Hz.
    destruct z as [| z]; try lia.
  Qed.

  (** A positive base raised to any exponent is positive. *)
  Lemma base_gt_zero_power_gt_zero :
    forall b e,
      0 < b
      -> 0 < b ^ e.
  Proof.
    intros b e Hlt; induction e as [| e IH]; simpl in *; auto.
    destruct b as [| b]; try lia.
  Qed.

  (** A digit value strictly less than the base at a lower position is less than any single digit at a higher position, capturing the positional-value argument. *)
  Lemma less_significant_value_lt_more_significant_digit :
    forall e2 e1 v b,
      v < b
      -> e1 < e2
      -> v * (b ^ e1) < b ^ e2.
  Proof.
    intros e2; induction e2 as [| e2 IH]; intros e1 v b Hvb Hee; sis; try lia.
    destruct b as [| b]; try lia.
    destruct e1 as [| e1].
    - rewrite Nat.mul_1_r.
      apply lt_lt_mul_nonzero_r; auto.
      apply base_gt_zero_power_gt_zero; lia.
    - rewrite Nat.pow_succ_r; try lia.
      rewrite <- Nat.mul_comm.
      rewrite <- Nat.mul_assoc.
      apply (proj1 (Nat.mul_lt_mono_pos_l (S b) _ _ ltac:(lia))).
      rewrite Nat.mul_comm.
      apply IH; lia.
  Qed.

  (** Set identity: adding [x] to the subtracted set is equivalent to removing [x] from the plain difference. *)
  Lemma diff_add_equal_remove_diff :
    forall x s s',
      NtSet.Equal (NtSet.diff s (NtSet.add x s'))
                  (NtSet.remove x (NtSet.diff s s')).
  Proof.
    intros x s s'; ND.fsetdec.
  Qed.

  (** Adding [x] to [s'] reduces the cardinality of [s ∖ s'] by 1, recording the push's effect on the exponent counter. *)
  Lemma cardinal_diff_minus_1 :
    forall x s s',
      NtSet.In x s
      -> ~ NtSet.In x s'
      -> S (NtSet.cardinal (NtSet.diff s (NtSet.add x s'))) =
         NtSet.cardinal (NtSet.diff s s').
  Proof.
    intros x s s' hi hn.
    rewrite diff_add_equal_remove_diff.
    apply remove_cardinal_1.
    apply NF.mem_iff; ND.fsetdec.
  Qed.
  
  (** The key push lemma: pushing a new frame for [x] strictly decreases the stack score because the new rhs length is bounded by [max_length] while the exponent drops by 1. *)
  Lemma stack_score_lt_after_push :
    forall all_rhss rhs caller_suf x suf' u vi locs,
      caller_suf = NT x :: suf'
      -> NtSet.In x u
      -> ~ NtSet.In x vi
      -> In rhs all_rhss
      -> stack_score (rhs, caller_suf :: locs)
                    (1 + max_length all_rhss)
                    (NtSet.cardinal (NtSet.diff u (NtSet.add x vi)))
         <
         stack_score (caller_suf, locs)
                    (1 + max_length all_rhss)
                    (NtSet.cardinal (NtSet.diff u vi)).
  Proof.
    intros all_rhss rhs cr_suf x suf' u vi locs
           hcr hi hn hi'; subst.
    pose proof (cardinal_diff_minus_1 x u vi hi hn) as Hcard.
    remember (1 + max_length all_rhss) as B eqn:HB.
    remember (NtSet.cardinal (NtSet.diff u (NtSet.add x vi))) as c eqn:Hc_def.
    assert (Hlt : length rhs * B ^ c < B ^ S c).
    { apply less_significant_value_lt_more_significant_digit.
      - rewrite HB; eapply mem_length_lt_max_plus_1; eauto.
      - lia. }
    unfold stack_score, head_frame_score, head_frame_size, tail_frame_score, tail_frame_size.
    rewrite <- Hcard.
    change (tail_frames_score ((NT x :: suf') :: locs) B (1 + c))
      with (length suf' * B ^ S c + tail_frames_score locs B (S (S c))).
    change (length (NT x :: suf')) with (S (length suf')).
    change (tail_frames_score locs B (1 + S c)) with (tail_frames_score locs B (S (S c))).
    assert (HCeq : S (length suf') * B ^ S c = B ^ S c + length suf' * B ^ S c) by ring.
    rewrite HCeq. lia.
  Qed.

  (*
  Lemma stack_score_lt_after_push' :
    forall all_rhss suf_cr rhs x u vi locs,
      NtSet.In x u
      -> ~ NtSet.In x vi
      -> In rhs all_rhss
      -> stack_score (rhs, suf_cr :: locs)
                    (1 + max_length all_rhss)
                    (NtSet.cardinal (NtSet.diff u (NtSet.add x vi)))
         <
         stack_score ((NT x :: suf_cr), locs)
                    (1 + max_length all_rhss)
                    (NtSet.cardinal (NtSet.diff u vi)).
  Proof.
    intros; eapply stack_score_lt_after_push; sis; eauto.
  Qed.
   *)
  
  (* A subparser invariant used to prove termination *)

  (** Invariant on the stack: every non-bottom frame was pushed because of a nonterminal [x] in the grammar's key set. *)
  Inductive pushes_from_keyset (rm : rhs_map) : list (list symbol) -> Prop :=
  | pk_bottom :
      forall suf,
        pushes_from_keyset rm [suf]
  | pk_upper :
      forall x suf suf' sufs,
        NtSet.In x (key_set rm)
        -> pushes_from_keyset rm (        (NT x :: suf) :: sufs)
        -> pushes_from_keyset rm (suf' :: (NT x :: suf) :: sufs).

  Hint Constructors pushes_from_keyset : core.
  
  (** Destructs a [pushes_from_keyset] hypothesis, naming the key-set membership and the sub-invariant. *)
  Ltac inv_pk hk  hi hk' := inversion hk as [? | ? ? ? ? hi hk']; subst; clear hk.
  
(*
  Definition sll_stack_lhss_from_keyset (rm : rhs_map) (stk : suffix_stack) : Prop :=
    match stk with
    | (fr, frs) => upper_lhss_from_keyset rm (fr :: frs)
    end.

  Definition sll_sp_lhss_from_keyset (rm : rhs_map) (sp : sll_subparser) : Prop :=
    match sp with
    | sll_sp _ stk => sll_stack_lhss_from_keyset rm stk
    end.

  Definition all_sll_sp_lhss_from_keyset (rm : rhs_map) (sps : list sll_subparser) :=
    forall sp, In sp sps -> sll_sp_lhss_from_keyset rm sp.

  Lemma sll_ulk_list__ulk_mem :
    forall rm sps sp,
      all_sll_sp_lhss_from_keyset rm sps
      -> In sp sps
      -> sll_sp_lhss_from_keyset rm sp.
  Proof.
    intros; auto.
  Qed.
 *)

  (** A return step (popping an empty callee frame) preserves the [pushes_from_keyset] invariant. *)
  Lemma return_preserves_keyset_invar :
    forall rm x suf frs,
      pushes_from_keyset rm ([] :: (NT x :: suf) :: frs)
      -> pushes_from_keyset rm (suf :: frs).
  Proof.
    intros rm x suf frs hk. 
    inv_pk hk hi hk'.
    inv hk'; auto.
  Qed.

  (** Consuming a terminal or nonterminal from the head frame preserves the [pushes_from_keyset] invariant. *)
  Lemma consume_preserves_keyset_invar :
    forall rm s suf frs,
      pushes_from_keyset rm ((s :: suf) :: frs)
      -> pushes_from_keyset rm (suf :: frs).
  Proof.
    intros rm suf suf' frs hk.
    inv_pk hk hi hk'; auto.
  Qed.

  (** Pushing a new frame for [x ∈ key_set rm] extends the invariant with a [pk_upper] constructor. *)
  Lemma push_preserves_keyset_invar :
    forall rm x suf suf' frs,
      NtSet.In x (key_set rm)
      -> pushes_from_keyset rm ((NT x :: suf) :: frs)
      -> pushes_from_keyset rm (suf' :: (NT x :: suf) :: frs).
  Proof.
    intros ? ? ? ? ? hi hk; inv hk; auto.
  Qed.
  
(*
  Lemma sll_return_preserves_keyset_invar :
    forall rm o_ce o_cr suf_ce suf_cr frs,
      upper_lhss_from_keyset rm (SF o_ce suf_ce :: SF o_cr suf_cr :: frs)
      -> upper_lhss_from_keyset rm (SF o_cr suf_cr :: frs).
  Proof.
    intros rm oce ocr sufce sufcr frs hk.
    inv_ulk hk hi hk'.
    inv_ulk hk' hi' hk''; auto.
  Qed.

  Lemma sll_consume_preserves_keyset_invar :
    forall rm o suf suf' frs,
      upper_lhss_from_keyset rm (SF o suf :: frs)
      -> upper_lhss_from_keyset rm (SF o suf' :: frs).
  Proof.
    intros rm o suf suf' frs hk. 
    inv_ulk hk hi hk'; auto.
  Qed.

  Lemma sll_push_preserves_keyset_invar :
    forall rm x o_cr suf_cr suf_cr' suf_ce frs,
      NtSet.In x (key_set rm)
      -> upper_lhss_from_keyset rm (SF o_cr suf_cr :: frs)
      -> upper_lhss_from_keyset rm (SF (Some x) suf_ce :: SF o_cr suf_cr' :: frs).
  Proof.
    intros ? ? ? ? ? ? ? hi hk; inv hk; auto.
  Qed.
 *)
  
  (* Now lift the invariant to LL subparser and parser stacks *)

  (** Lifts [pushes_from_keyset] to a suffix stack represented as a head-frame / tail-frames pair. *)
  Definition suffix_stack_pushes_from_keyset (rm : rhs_map) (stk : list symbol * list (list symbol)) : Prop :=
    match stk with
    | (fr, frs) =>
      pushes_from_keyset rm (fr :: frs)
    end.

  (*
  Definition sp_lhss_from_keyset (rm : rhs_map) (sp : subparser) : Prop :=
    sll_sp_lhss_from_keyset rm (sllify_sp sp).

  Definition all_sp_lhss_from_keyset (rm : rhs_map) (sps : list subparser) : Prop :=
    forall sp, In sp sps -> sp_lhss_from_keyset rm sp.

  Lemma ulk_list__ulk_mem :
    forall rm sps sp,
      all_sp_lhss_from_keyset rm sps
      -> In sp sps
      -> sp_lhss_from_keyset rm sp.
  Proof.
    intros; auto.
  Qed.

   *)
  
  (* A measure function *)

  (** The lexicographic termination measure: a pair of (stack score, stack height) that strictly decreases on every parser step. *)
  Definition meas (rm : rhs_map) (vi : NtSet.t) (sk : list symbol * list (list symbol)) : nat * nat :=
    let m  := max_length (all_rhss rm) in
    let e  := NtSet.cardinal (NtSet.diff (key_set rm) vi)
    in  (stack_score sk (1 + m) e, stack_height sk).

  (** The measure strictly decreases on a return step: the stack score is non-increasing and the height drops by 1. *)
  Lemma meas_lt_after_return :
    forall rm sk sk' vi vi' x suf frs,
      sk = ([], (NT x :: suf) :: frs)
      -> sk' = (suf, frs)
      -> vi' = NtSet.remove x vi
      -> suffix_stack_pushes_from_keyset rm sk
      -> lex_nat_pair (meas rm vi' sk') (meas rm vi sk).
  Proof.
    intros rm sk sk' vi vi' x suf frs ? ? ? hk; subst.
    unfold meas.
    pose proof stack_score_le_after_return' as hle.
    specialize hle with (suf := suf) (x := x).
    assert (hki : NtSet.In x (key_set rm)) by (inv hk; auto).
    specialize (hle (1 + max_length (all_rhss rm)) vi (key_set rm) frs hki).
    apply Nat.le_lteq in hle.
    destruct hle as [hlt | heq]; sis.
    - apply left_slex; auto.
    - rewrite heq; apply right_slex; simpl; lia.
  Defined.

  (** The measure strictly decreases on a push step: adding [x] to the visited set reduces the score's exponent, outweighing the new frame's contribution. *)
  Lemma meas_lt_after_push :
    forall rm vi vi' sk sk' fr_cr fr_ce x suf rhs frs,
      sk     = (fr_cr, frs)
      -> sk' = (fr_ce, fr_cr :: frs)
      -> fr_cr  = NT x :: suf
      -> fr_ce  = rhs
      -> vi' = NtSet.add x vi
      -> ~ NtSet.In x vi
      -> NtSet.In x (key_set rm)
      -> In rhs (all_rhss rm)
      -> lex_nat_pair (meas rm vi' sk') (meas rm vi sk).
  Proof.
    intros; subst.
    apply left_slex.
    eapply stack_score_lt_after_push; sis; eauto.
  Defined.

(*
  Definition sll_meas (rm : rhs_map) (vi : NtSet.t) (sp : sll_subparser) : nat * nat :=
    match sp with
    | sll_sp _ stk =>
      let m  := max_length (all_rhss rm) in
      let e  := NtSet.cardinal (NtSet.diff (key_set rm) vi)
      in  (stack_score (sllSuffixes stk) (1 + m) e, stack_height stk)
    end.

  Lemma sll_meas_lt_after_return :
    forall rm sp sp' vi vi' pred o suf x frs,
      sp = sll_sp pred (SF (Some x) [], SF o suf :: frs)
      -> sp' = sll_sp pred (SF o suf, frs)
      -> vi' = NtSet.remove x vi
      -> sll_sp_lhss_from_keyset rm sp
      -> lex_nat_pair (sll_meas rm vi' sp') (sll_meas rm vi sp).
  Proof.
    intros rm sp sp' vi vi' pred o suf x frs ? ? ? hk; subst.
    pose proof stack_score_le_after_return' as hle.
    specialize hle with (suf_cr := suf) (x := x).
    eapply le_lt_or_eq in hle; eauto.
    destruct hle as [hlt | heq]; sis.
    - apply left_slex; eauto.
    - rewrite heq; apply right_slex; auto.
    - inv hk; auto. 
  Defined.

  Lemma sll_meas_lt_after_push :
    forall rm vi vi' sp sp' pred fr_cr fr_cr' fr_ce o x suf rhs frs,
      sp     = sll_sp pred (fr_cr, frs)
      -> sp' = sll_sp pred (fr_ce, fr_cr' :: frs)
      -> fr_cr  = SF o (NT x :: suf)
      -> fr_cr' = SF o suf
      -> fr_ce  = SF (Some x) rhs
      -> vi' = NtSet.add x vi
      -> ~ NtSet.In x vi
      -> NtSet.In x (key_set rm)
      -> In rhs (all_rhss rm)
      -> lex_nat_pair (sll_meas rm vi' sp') (sll_meas rm vi sp).
  Proof.
    intros; subst.
    apply left_slex.
    eapply stack_score_lt_after_push; sis; eauto.
  Defined.
  *)

  (** Lifts the keyset invariant to a full LL parser stack via its suffix projection. *)
  Definition stack_pushes_from_keyset (rm : rhs_map) (stk : parser_stack) :=
    suffix_stack_pushes_from_keyset rm (stack_suffixes stk).

  (** The keyset invariant for a single LL subparser: its stack satisfies [stack_pushes_from_keyset]. *)
  Definition sp_pushes_from_keyset (rm : rhs_map) (sp : subparser) : Prop :=
    match sp with
    | Sp _ stk => stack_pushes_from_keyset rm stk
    end.

  (** States that every subparser in a list satisfies the keyset invariant. *)
  Definition all_sp_pushes_from_keyset (rm : rhs_map) (sps : list subparser) : Prop :=
    forall sp, In sp sps -> sp_pushes_from_keyset rm sp.

  (** Extracts the per-subparser keyset invariant from the list-level invariant given a membership proof. *)
  Lemma pki_list__pki_mem :
    forall rm sps sp,
      all_sp_pushes_from_keyset rm sps
      -> In sp sps
      -> sp_pushes_from_keyset rm sp.
  Proof.
    intros; auto.
  Qed.

  (* Lift the invariant to SLL stacks and subparsers *)

  (** Lifts the keyset invariant to an SLL stack via its suffix projection. *)
  Definition sll_stack_pushes_from_keyset (rm : rhs_map) (stk : sll_stack) :=
    suffix_stack_pushes_from_keyset rm (sll_stack_suffixes stk).

  (** The keyset invariant for a single SLL subparser: its stack satisfies [sll_stack_pushes_from_keyset]. *)
  Definition sll_sp_pushes_from_keyset (rm : rhs_map) (sp : sll_subparser) : Prop :=
    match sp with
    | sll_sp _ stk => sll_stack_pushes_from_keyset rm stk
    end.

  (** States that every SLL subparser in a list satisfies the keyset invariant. *)
  Definition all_sll_sp_pushes_from_keyset (rm : rhs_map) (sps : list sll_subparser) : Prop :=
    forall sp, In sp sps -> sll_sp_pushes_from_keyset rm sp.

  (** Extracts the per-SLL-subparser keyset invariant from the list-level invariant given a membership proof. *)
  Lemma sll_pki_list__pki_mem :
    forall rm sps sp,
      all_sll_sp_pushes_from_keyset rm sps
      -> In sp sps
      -> sll_sp_pushes_from_keyset rm sp.
  Proof.
    intros; auto.
  Qed.
  
End TerminationFn.
