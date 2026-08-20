(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.

From Stdlib Require Import Lia PeanoNat.

From Crane.Libraries.ParseALot.Utils Require Import Ltac.

From Crane.Libraries.ParseALot.Lexer Require Import State.
From Crane.Libraries.ParseALot.Lexer.Lexer Require Import Abstraction.


(** Module type specifying user-supplied semantic actions that interpret tokens into typed values. *)
Module Type SemUser (Import STT : State.T).

  Import STT.R.Defs.
  Import STT.R.
  Import STT.Defs.
  Import STT.Ty.

  Parameter sem_ty : Label -> Type.
  Parameter apply_sem : (Label * String) -> option {l : Label & sem_ty l}.
  Parameter label_carries : forall l l' s t,
      apply_sem (l, s) = Some (existT _ l' t)
      -> l = l'.
  Parameter defLiteral : sem_ty defLabel.

End SemUser.

(** Functor building a semantic lexer by composing a raw lexer [LXR] with user semantic actions [USER]. *)
Module SemLexerFn (STT : State.T) (Export LXR : Lexer STT) (Import USER : SemUser STT).


  (** Core type definitions for semantic tokens. *)
  Module Import Core.

    (** A semantic token is a dependent pair of a label and a value of its associated type. *)
    Definition sem_token := {l : Label & sem_ty l}.
    (** Default semantic token using [defLabel] and [defLiteral]. *)
    Definition defSemToken := (existT sem_ty defLabel defLiteral).

  End Core.

  (** Inductive specification relating token lists to semantic token lists via [apply_sem]. *)
  Module Import Spec.

    (** [tokenized_sem rus code o rest] holds when [o] is the semantic interpretation of the tokenization of [code]. *)
    Inductive tokenized_sem (rus : list Rule) : String -> (option (list sem_token))
                                                -> String -> Prop :=
    | Tkd_sem_Some (code rest : String) (ts : list Token) (sts : list sem_token)
                   (H0 : tokenized rus code ts rest)
                   (H1 : length ts = length sts)
                   (H2 : forall t st,  In (t, st) (combine ts sts)
                                  -> apply_sem t = Some st)
      : tokenized_sem rus code (Some sts) rest
    | Tkd_sem_None (code rest : String) (ts : list Token)
        (H : tokenized rus code ts rest)
        (Hin : exists t, In t ts /\ apply_sem t = None)
      : tokenized_sem rus code None rest.

  End Spec.

  (** Implementation of the semantic lexer functions. *)
  Module Import Impl.

    (** Runs the raw lexer and maps [apply_sem] over each token, returning a list of options. *)
    Definition lex_sem' (rus : list Rule) (code : String) : (list (option sem_token)) * String :=
      match lex rus code with
      | (ts, rest) => ((map apply_sem ts), rest)
      end.

    (** Converts a [list (option A)] to an [option (list A)], returning [None] if any element is [None]. *)
    Fixpoint lo2ol {A : Type} (xs : list (option A)) : option (list A) :=
      match xs with
      | [] => Some []
      | None :: ys => None
      | Some x :: ys =>
        match lo2ol ys with
        | None => None
        | Some zs => Some (x :: zs)
        end
      end.

    (** Semantic lexer: runs [lex_sem'] then collects results with [lo2ol], returning [None] on any failed action. *)
    Definition lex_sem (rus : list Rule) (code : String) : (option (list sem_token)) * String :=
      match lex_sem' rus code with
      | (ts, rest) => (lo2ol ts, rest)
      end.

  End Impl.

  (** Auxiliary lemmas about [lo2ol] and the interaction between [apply_sem] and list combinators. *)
  Module Import Lemmas.

    (** [lo2ol xs = None] iff [None] appears in [xs]; by induction on [xs]. *)
    Lemma lo2ol_None : forall {T : Type} (xs : list (option T)),
      lo2ol xs = None
      <-> In None xs.
    Proof.
      intros; split; intros.
      {
        induction xs.
        - sis. discriminate.
        - sis. repeat dm. discriminate.
      }
      {
        induction xs.
        - sis. contradiction.
        - sis. repeat dm. destruct H.
          + discriminate.
          + apply IHxs in H. discriminate.
      }
    Qed.

    (** If [lo2ol (x::xs) = Some (y::ys)], then [lo2ol xs = Some ys]; by case analysis. *)
    Lemma lo2ol_tail : forall {T : Type} (ys : list T) (xs : list (option T)) x y,
        lo2ol (x :: xs) = Some (y :: ys)
        -> lo2ol xs = Some ys.
    Proof.
      destruct xs; intros.
      {
        sis. repeat dm.
        - repeat inj_all. auto.
        - discriminate.
      }
      {
        sis. repeat dm; repeat inj_all; auto; try discriminate.
      }
    Qed.

    (** If [lo2ol (x::xs) = Some (y::ys)], then [x = Some y]; by case analysis. *)
    Lemma lo2ol_head : forall {T : Type} (ys : list T) (xs : list (option T)) x y,
        lo2ol (x :: xs) = Some (y :: ys)
        -> x = Some y.
    Proof.
      intros. sis. repeat dm.
      - repeat inj_all. auto.
      - discriminate.
      - discriminate.
    Qed.

    (** If [lo2ol xs = Some ys], then [length xs = length ys]; by induction using [lo2ol_tail]. *)
    Lemma lo2ol_length : forall {T : Type} (xs : list (option T)) (ys : list T),
      lo2ol xs = Some ys
      -> length xs = length ys.
    Proof.
      induction xs; intros.
      {
        sis. inv H. auto.
      }
      {
        destruct ys.
        - sis. repeat dm; repeat inj_all; discriminate.
        - apply lo2ol_tail in H. apply IHxs in H. sis. lia.
      }
    Qed.

    (* this could be more general *)
    (** If [map apply_sem l1 = l0], [lo2ol l0 = Some l], and [(t,st)] is in [combine l1 l], then [apply_sem t = Some st]. *)
    Lemma lo2ol_map : forall l1 l0 l t st,
        map apply_sem l1 = l0
        -> lo2ol l0 = Some l
        -> In (t, st) (combine l1 l)
        -> apply_sem t = Some st.
    Proof.
      induction l1; intros.
      {
        sis. contradiction.
      }
      {
        destruct l0. sis. discriminate. destruct l. sis. repeat dm; discriminate.
        destruct H1.
        - repeat inj_all. rewrite map_cons in H. injection H; intros.
          rewrite H2. apply lo2ol_head in H0. auto.
        - eapply IHl1; eauto.
          rewrite <- H in H0. eapply lo2ol_tail; eauto.
      }
    Qed.

    (** If every entry in [combine ts sts] satisfies [apply_sem], and lengths match, then [Some sts = lo2ol (map apply_sem ts)]. *)
    Lemma In_combine_lo2ol_map : forall ts sts,
        (forall (t : Token) (st : sem_token), In (t, st) (combine ts sts)
                                         -> apply_sem t = Some st)
        -> length ts = length sts
        -> Some sts = lo2ol (map apply_sem ts).
    Proof.
      induction ts; destruct sts; try (sis; lia); auto; intros.
      inv H0. apply IHts in H2.
      - sis. repeat dm.
        + repeat inj_all. specialize (H a s).
          assert((a, s) = (a, s) \/ In (a, s) (combine ts l)).
          { auto. }
          apply H in H0. rewrite E in *. inv H0. auto.
        + discriminate.
        + specialize (H a s).
          assert((a, s) = (a, s) \/ In (a, s) (combine ts sts)).
          { auto. }
          apply H in H0. rewrite H0 in *. discriminate.
      - intros. apply H. simpl. auto.
    Qed.


  End Lemmas.

  (** Soundness, uniqueness, and completeness theorems for [lex_sem]. *)
  Module Correct.


    (** [lex_sem] output satisfies [tokenized_sem]; proven by combining [lex_sound] with [lo2ol] properties. *)
    Theorem lex_sem_sound : forall o code rest rus,
      lex_sem rus code = (o, rest)
      -> rules_is_function rus
      -> tokenized_sem rus code o rest.
    Proof.
      intros.
      unfold lex_sem in *. repeat dm. unfold lex_sem' in *. repeat dm.
      assert(tokenized rus code l0 rest).
      {
        repeat inj_all. eapply lex_sound; eauto.
      }
      destruct o.
      {
        eapply Tkd_sem_Some; eauto.
        - repeat inj_all. apply lo2ol_length in H3. rewrite length_map in H3. auto.
        - intros. eapply lo2ol_map; eauto. repeat inj_all. auto.
      }
      {
        eapply Tkd_sem_None; eauto.
        repeat inj_all. apply lo2ol_None in H3.
        apply in_map_iff in H3. destruct H3. exists x.
        destruct H. split; auto.
      }
    Qed.

    (** Any two [tokenized_sem] witnesses for the same input agree; proven via [lex_complete] and [In_combine_lo2ol_map]. *)
    Theorem tokenized_sem_unique : forall rus code o rest o0 s,
        tokenized_sem rus code o rest
        -> rules_is_function rus
        -> tokenized_sem rus code o0 s
        -> (o, rest) = (o0, s).
    Proof.
      intros. inv H; inv H1.
      - assert(ts = ts0 /\ rest = s).
        {
          apply lex_complete in H2; auto. apply lex_complete in H5; auto.
          rewrite H2 in H5. repeat inj_all. auto.
        }
        destruct H. subst. clear H2 H5 rus code H0.
        apply In_combine_lo2ol_map in H7; auto. apply In_combine_lo2ol_map in H4; auto.
        rewrite <- H7 in *. rewrite H4. auto.
      - assert(ts = ts0 /\ rest = s).
        {
          apply lex_complete in H2; auto. apply lex_complete in H; auto.
          rewrite H2 in H. repeat inj_all. auto.
        }
        destruct H1. subst. destruct Hin. destruct H1.
        apply In_nth with (d := (defLabel, [])) in H1.
        destruct H1. destruct H1.
        assert(nth x0 sts defSemToken = nth x0 sts defSemToken).
        { auto. }
        assert(x0 < length (combine ts0 sts)).
        { rewrite length_combine. rewrite <- H3. rewrite Nat.min_id. auto. }
        eapply combine_nth with (n := x0) (x := (defLabel, [])) (y := defSemToken)
          in H3.
        eapply nth_In in H8. rewrite H3 in H8.
        apply H4 in H8. rewrite H6 in *. rewrite H8 in *. discriminate.
      - assert(ts = ts0 /\ rest = s).
        {
          apply lex_complete in H2; auto. apply lex_complete in H3; auto.
          rewrite H2 in H3. repeat inj_all. auto.
        }
        destruct H. subst. destruct Hin. destruct H.
        apply In_nth with (d := (defLabel, [])) in H.
        destruct H. destruct H.
        assert(nth x0 sts defSemToken = nth x0 sts defSemToken).
        { auto. }
        assert(x0 < length (combine ts0 sts)).
        { rewrite length_combine. rewrite <- H4. rewrite Nat.min_id. auto. }
        eapply combine_nth with (n := x0) (x := (defLabel, [])) (y := defSemToken)
          in H4.
        eapply nth_In in H8. rewrite H4 in H8.
        rewrite H6 in H8. apply H5 in H8. rewrite H1 in *. discriminate.
      - assert(ts = ts0 /\ rest = s).
        {
          apply lex_complete in H2; auto. apply lex_complete in H; auto.
          rewrite H2 in H. repeat inj_all. auto.
        }
        destruct H1. subst. auto.
    Qed.


    (** [lex_sem] output is fully determined by [tokenized_sem]; proven via [lex_sem_sound] and [tokenized_sem_unique]. *)
    Theorem lex_sem_complete : forall o code rest rus,
      tokenized_sem rus code o rest
      -> rules_is_function rus
      -> lex_sem rus code = (o, rest).
    Proof.
      intros. destruct (lex_sem rus code) eqn:E.
      eapply lex_sem_sound in E; eauto.
      eapply tokenized_sem_unique; eauto.
    Qed.



  End Correct.

End SemLexerFn.
