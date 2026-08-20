(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import PeanoNat Wf_nat.
From Stdlib Require Import Lia.
From Stdlib Require Import Numbers.NatInt.NZOrder.

From Crane.Libraries.ParseALot.Utils Require Import Ltac.
From Crane.Libraries.ParseALot.Lexer Require Import State.
From Crane.Libraries.ParseALot.Lexer.Lexer Require Import LemmasPref.
From Crane.Libraries.ParseALot.Lexer.Lexer Require Import ImplPref.

(** Concrete lexer implementation: well-founded recursive tokenisation loop. *)
Module ImplFn (Import ST : State.T).

  Import ST.Ty.
  Import ST.Defs.
  (** Local alias for the prefix-lemmas functor instantiated at [ST]. *)
  Module Lem := LemmasPref.LemmasFn ST.
  Import Lem.
  Import Lem.Impl.


  (** Exports the [lex] and [lex'] definitions together with their termination witnesses. *)
  Module Export Lex.

    (** Accessibility of the recursive call's suffix: its length is strictly smaller than [code]'s, by [proper_suffix_shorter]. *)
    Lemma acc_recursive_call :
      forall code rules label s l suffix i i',
        Acc lt (length code)
        -> max_of_prefs (max_prefs code i rules) = (label, Some (s :: l, suffix, i'))
        -> Acc lt (length suffix).
    Proof.
      intros code rules label s l suffix i i' Ha Heq.
      apply Acc_inv with (x := length code).
      - apply Ha.
      - assert(A2 : exists(fsm : State), Some (s :: l, suffix, i')
                                    = max_pref_fn code i fsm).
        {
          induction rules.
          - simpl in Heq. discriminate.
          - symmetry in Heq. apply max_first_or_rest in Heq. destruct Heq.
            + destruct a. simpl in H. exists s0. injection H; intros; subst. apply H0.
            + apply IHrules. destruct rules.
              * simpl in H. discriminate.
              * rewrite H. reflexivity.
        }
        assert(A3 : s :: l <> []).
        { intros C. discriminate. }
        destruct A2 as (fsm & A2).
        eapply proper_suffix_shorter with (suffix := suffix) (code := code)
                                         (fsm := fsm) in A3; eauto.
    Defined.


    (** The index carried into the recursive call equals [init_index (length suffix)]; by [index_closure_gen]. *)
    Lemma index_rec_call_gen : forall code rules i suffix i' z label,
        i = init_index (length code)
        -> max_of_prefs (max_prefs code i rules) = (label, Some (z, suffix, i'))
        -> i' = init_index (length suffix).
    Proof.
      intros.
      rewrite H in *. apply exists_rus_of_mpref_gen in H0. destruct H0 as (r & Hin & E2).
      symmetry in E2. apply index_closure_gen in E2. auto.
    Qed.


    (** Specialisation of [index_rec_call_gen] to the non-empty prefix case used in [lex']. *)
    Lemma index_rec_call : forall rules code i suffix i' ph pt label,
        i = init_index (length code)
        -> max_of_prefs (max_prefs code i rules) = (label, Some (ph :: pt, suffix, i'))
        -> i' = init_index (length suffix).
    Proof.
      intros. eapply index_rec_call_gen; eauto.
    Defined.

    (** Well-founded recursive lexer: consumes the longest matching token at each step until no rule applies. *)
    Fixpoint lex'
             (rules : list sRule)
             (code : String)
             (i : index)
             (Hindex : i = init_index (length code))
             (Ha : Acc lt (length code))
             {struct Ha} : (list Token) * String :=
      match max_of_prefs (max_prefs code i rules) as mpref'
            return max_of_prefs (max_prefs code i rules) = mpref' -> _
      with
      | (_, None) => fun _ => ([], code) (* Code cannot be processed further *)
      | (_, Some ([], _, _)) => fun _ => ([], code) (* Code cannot be processed further *)
      | (label, Some (ph :: pt, suffix, i')) =>
        fun Heq =>
          match (lex' rules suffix i'
                      (index_rec_call _ _ _ _ _ _ _ _ Hindex Heq)
                      (acc_recursive_call _ _ _ _ _ _ _ _ Ha Heq)) with
          | (lexemes, rest) => (((label, ph :: pt) :: lexemes), rest)
          end
      end eq_refl.
    (**)

    (** Top-level lexer: initialises FSM states from raw rules and invokes [lex'] under [lt_wf]. *)
    Definition lex (rules : list Rule) (code : String) :=
      let
        srules := map init_srule rules
      in
      lex' srules code (init_index (length code)) eq_refl (lt_wf _).

  End Lex.

End ImplFn.
