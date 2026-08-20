(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Program.Wf.
From Stdlib Require Import Lia Wf_nat.

From Stdlib Require Import NArith Pnat PeanoNat.
From Stdlib Require Import SetoidList FSets.

From Crane.Libraries.ParseALot.Utils Require Import Ltac.
From Crane.Libraries.ParseALot.Lexer Require Import Regex.

(** Abstract interface for a DFA transition table indexed by (regex, symbol) pairs. *)
Module Type Table (R : Regex.T).

  Import R.Ty.
  Module Import DS := R.Defs.
  Module Import reFS := DS.reFS.

  Parameter Table : Type.
  Parameter emptyTable : Table.
  (*The first regex is for indexing, the second is the content of the cell*)
  Parameter set_Table : Table -> regex -> Sigma -> regex -> Table.
  Parameter get_Table : Table -> regex -> Sigma -> option (regex).

  Parameter correct_Table : forall T e a r, get_Table (set_Table T e a r) e a = Some (r).
  Parameter moot_setTable : forall T e0 e a b r,
      a <> b
      \/ e <> e0
      -> get_Table (set_Table T e b r) e0 a = get_Table T e0 a.
  Parameter correct_emptyTable : forall e a, get_Table emptyTable e a = None.


  Parameter add_state : Table -> regex -> Table.
  Parameter get_states : Table -> t.
  Parameter empty_states : get_states emptyTable = empty.
  Parameter correct_states : forall T r, In r (get_states (add_state T r)).
  Parameter moot_add_state : forall T e a r,
      get_Table T e a = get_Table (add_state T r) e a.
  (* might need a hypothesis about not being in states *)


  Parameter get_eq : Table -> regex -> option regex.

  Parameter get_eq_correct : forall T e e',
      get_eq T e = Some e' -> In e' (get_states T) /\ regex_eq e e' = true.

  (** The following four are what the table fill's completeness proof needs on
      top of the original interface: that [add_state] adds exactly one state,
      that [set_Table] adds none, and that [get_eq] answering [None] really
      means the state is absent (so each [None] branch of the fill makes
      progress). *)
  Parameter add_state_states : forall T r x,
      In x (get_states (add_state T r)) -> x = r \/ In x (get_states T).
  Parameter add_state_mono : forall T r x,
      In x (get_states T) -> In x (get_states (add_state T r)).
  Parameter set_Table_states : forall T e a r,
      get_states (set_Table T e a r) = get_states T.
  Parameter get_eq_None : forall T e,
      get_eq T e = None -> ~ In e (get_states T).
  Parameter add_state_cardinal : forall T r,
      ~ In r (get_states T) ->
      cardinal (get_states (add_state T r)) = S (cardinal (get_states T)).

End Table.

(** Functor implementing Brzozowski derivative table filling and the [derived] invariant. *)
Module DefsFn (R : Regex.T) (TabTy : Table R).

  Import TabTy.
  Import R.Defs.
  Import R.Ty.

  (** Definitions for filling a DFA transition table with Brzozowski derivatives. *)
  Module Export FillTable.

    Import R.Defs.Helpers.

    (* Assume all union inputs are already canonical:
       1. All iterared unions are recursively right associated
       2. All iterated unions are in lexicographic order
       3. The EmptySet is not present in any union
       4. All regexes in all iterated unions are unique
     *)
    (** Flattens a right-recursive iterated union into a list of its branches. *)
    Fixpoint mkIterUnion' (e : regex) : list regex :=
      match e with
      | Union e1 e2 =>
        e1 :: (mkIterUnion' e2)
      | _ => [e]
      end.

    (**
    (* automation *)
    Program Fixpoint merge (es1 es2 : list regex)
            { measure ((length es1) + (length es2)) } : list regex :=
      match es1, es2 with
      | [], _ => es2
      | _, [] => es1
      | h1 :: t1, h2 :: t2 =>
        match re_compare h1 h2 with
        | Eq => merge (h1 :: t1) t2
        | Lt => h1 :: (merge t1 (h2 :: t2))
        | Gt => h2 :: (merge (h1 :: t1) t2)
        end
      end.
    Next Obligation.
      simpl. lia.
    Defined.
    Next Obligation.
      simpl. lia.
    Defined.

    (* issues unfolding things *)
    Lemma merge_cons : forall t1 t2 h1 h2,
        match re_compare h1 h2 with
        | Eq => merge (h1 :: t1) (h2 :: t2) = merge (h1 :: t1) t2
        | Lt => merge (h1 :: t1) (h2 :: t2) = h1 :: (merge t1 (h2 :: t2))
        | Gt => merge (h1 :: t1) (h2 :: t2) =  h2 :: (merge (h1 :: t1) t2)
        end.
    Proof.
      intros. dm.
      - unfold merge. unfold merge_func. rewrite fix_sub_eq.
        + simpl. rewrite E. auto.
        + intros. destruct x. induction x.
          * auto.
          *
    Abort.
     *)



    (* acc proof method, issues type checking *)
    (** Accessibility witness for the first recursive call of merge (skip duplicate from right list). *)
    Lemma merge_acc1 :
      forall es1 es2 t1 t2 (h1 h2 : regex),
        Acc lt (length es1 + length es2)
        -> (es1, es2) = (h1 :: t1, h2 :: t2)
        -> Acc lt ((length (h1 :: t1)) + (length t2)).
    Proof.
      intros. inv H0. inv H. apply H0. simpl. lia.
    Defined.


    (** Accessibility witness for the second recursive call of merge (take from left list). *)
    Lemma merge_acc2 :
      forall es1 es2 t1 t2 (h1 h2 : regex),
        Acc lt (length es1 + length es2)
        -> (es1, es2) = (h1 :: t1, h2 :: t2)
        -> Acc lt ((length t1) + (length (h2 :: t2))).
    Proof.
      intros. inv H0. inv H. auto.
    Defined.


    (** Accessibility witness for the third recursive call of merge (take from right list); alias of [merge_acc1]. *)
    Lemma merge_acc3 :
      forall es1 es2 t1 t2 (h1 h2 : regex),
        Acc lt (length es1 + length es2)
        -> (es1, es2) = (h1 :: t1, h2 :: t2)
        -> Acc lt ((length (h1 :: t1)) + (length t2)).
    Proof.
      apply merge_acc1.
    Defined.


    (** Sorted merge of two regex lists, deduplicating equal elements; terminates by accessibility on combined length. *)
    Fixpoint merge' (es1 es2 : list regex)
            (Ha : Acc lt ((length es1) + (length es2)))
            {struct Ha} : list regex :=
      match (es1, es2) as tpl return (es1, es2) = tpl -> _ with
      | ([], _) => fun _ => es2
      | (_, []) => fun _ => es1
      | (h1 :: t1, h2 :: t2) =>
        fun Heq =>
        match re_compare h1 h2 with
        | Eq => merge' (h1 :: t1) t2 (merge_acc1 _ _ _ _ _ _ Ha Heq)
        | Lt => h1 :: (merge' t1 (h2 :: t2) (merge_acc2 _ _ _ _ _ _ Ha Heq))
        | Gt => h2 :: (merge' (h1 :: t1) t2 (merge_acc3 _ _ _ _ _ _ Ha Heq))
        end
      end eq_refl.

    (* Beginning of Sam's contributions *)

    (* lemma for unfolding merge' *)
    (** Unfolds one step of [merge'] by destructuring its [Acc] witness. *)
    Lemma merge'_eq_body :
      forall (es1 es2 : list regex)
             (Ha : Acc lt (length es1 + length es2)),
        merge' es1 es2 Ha =
        match (es1, es2) as tpl return (es1, es2) = tpl -> _ with
        | ([], _) => fun _ => es2
        | (_, []) => fun _ => es1
        | (h1 :: t1, h2 :: t2) =>
          fun Heq =>
            match re_compare h1 h2 with
            | Eq => merge' (h1 :: t1) t2 (merge_acc1 _ _ _ _ _ _ Ha Heq)
            | Lt => h1 :: (merge' t1 (h2 :: t2) (merge_acc2 _ _ _ _ _ _ Ha Heq))
            | Gt => h2 :: (merge' (h1 :: t1) t2 (merge_acc3 _ _ _ _ _ _ Ha Heq))
            end
        end eq_refl.
    Proof.
      intros; destruct Ha; auto.
    Qed.

    (* The original lemma you wanted to prove,
       although it's complicated a bit by proof terms *)
    (** Case split of [merge'] on the comparison of the two head elements, exposing the concrete recursive call. *)
    Lemma merge'_cons :
      forall t1 t2 h1 h2 Ha,
        match re_compare h1 h2 with
        | Eq => merge' (h1 :: t1) (h2 :: t2) Ha =
                merge' (h1 :: t1) t2 (merge_acc1 _ _ _ _ _ _ Ha eq_refl)
        | Lt => merge' (h1 :: t1) (h2 :: t2) Ha =
                h1 :: merge' t1 (h2 :: t2) (merge_acc2 _ _ _ _ _ _ Ha eq_refl)
        | Gt => merge' (h1 :: t1) (h2 :: t2) Ha =
                h2 :: merge' (h1 :: t1) t2 (merge_acc3 _ _ _ _ _ _ Ha eq_refl)
        end.
    Proof.
      intros t1 t2 h1 h2 Ha; rewrite merge'_eq_body; dm.
    Qed.

    (* You can also define a top-level function that calls
       merge' with the right initial Acc term *)
    (** Top-level sorted merge that supplies the canonical [lt_wf] accessibility term. *)
    Definition merge'' (es1 es2 : list regex) : list regex :=
      merge' es1 es2 (lt_wf _).

    (* If you naively start to prove things about it,
       though, you run into trouble *)
    (** Case split for [merge''] analogous to [merge'_cons]; aborted due to differing proof terms. *)
    Lemma merge''_cons :
      forall t1 t2 h1 h2,
        match re_compare h1 h2 with
        | Eq => merge'' (h1 :: t1) (h2 :: t2) = merge'' (h1 :: t1) t2
        | Lt => merge'' (h1 :: t1) (h2 :: t2) = h1 :: merge'' t1 (h2 :: t2)
        | Gt => merge'' (h1 :: t1) (h2 :: t2) = h2 :: merge'' (h1 :: t1) t2
        end.
    Proof.
      intros t1 t2 h1 h2.
      unfold merge''.
      dm.
      - (* uh-oh, the proof terms are different *)
    Abort.

    (* We need to prove that the function's input/output
       behavior doesn't depend on the Acc term
       (seems obvious, but I don't think the general fact
       is provable within Coq) *)
    (** [merge'] output is independent of the [Acc] witness, proved by well-founded induction on combined length. *)
    Lemma merge'_ignores_acc' :
      forall len es1 es2 (Ha Ha' : Acc lt (length es1 + length es2)),
        len = length es1 + length es2
        -> merge' es1 es2 Ha = merge' es1 es2 Ha'.
    Proof.
      intros len.
      induction len as [len IH] using lt_wf_ind; intros es1 es2 Ha Ha' Heq; subst.
      repeat rewrite merge'_eq_body.
      destruct es1 as [| h1 t1]; auto.
      destruct es2 as [| h2 t2]; auto.
      destruct (re_compare h1 h2) eqn:Heq.
      - apply IH with (m := length (h1 :: t1) + length t2); auto.
        simpl; lia.
      - erewrite IH with (m := length t1 + length (h2 :: t2)); eauto.
      - erewrite IH with (m := length (h1 :: t1) + length t2); eauto.
        simpl; lia.
    Qed.

    (** [merge'] output is independent of the [Acc] witness; convenience wrapper around [merge'_ignores_acc']. *)
    Lemma merge'_ignores_acc :
      forall es1 es2 (Ha Ha' : Acc lt (length es1 + length es2)),
        merge' es1 es2 Ha = merge' es1 es2 Ha'.
    Proof.
      intros; eapply merge'_ignores_acc'; eauto.
    Qed.

    (* Now we can prove the lemma you wanted about the
       top-level function (this proof could be automated,
       but I set it up so you can step through if you're
       curious) *)
    (** Case split for [merge''] on the head comparison; proved using [merge'_ignores_acc] to bridge the [Acc] terms. *)
    Lemma merge''_cons :
      forall t1 t2 h1 h2,
        match re_compare h1 h2 with
        | Eq => merge'' (h1 :: t1) (h2 :: t2) = merge'' (h1 :: t1) t2
        | Lt => merge'' (h1 :: t1) (h2 :: t2) = h1 :: merge'' t1 (h2 :: t2)
        | Gt => merge'' (h1 :: t1) (h2 :: t2) = h2 :: merge'' (h1 :: t1) t2
        end.
    Proof.
      intros t1 t2 h1 h2.
      unfold merge''.
      pose proof (merge'_cons t1 t2 h1 h2) as Hmc.
      dm.
      - rewrite Hmc.
        erewrite merge'_ignores_acc. eauto.
      - rewrite Hmc.
        erewrite merge'_ignores_acc; eauto.
      - rewrite Hmc.
        erewrite merge'_ignores_acc; eauto.
    Qed.

    (* End of Sam's contributions *)

    (* Cleanly pack those contributions *)
    (** Canonical sorted merge of two regex lists, deduplicating via [merge'']. *)
    Definition merge := merge''.

    (** Case split lemma for [merge] on head element comparison; delegates to [merge''_cons]. *)
    Lemma merge_cons :
      forall t1 t2 h1 h2,
        match re_compare h1 h2 with
        | Eq => merge (h1 :: t1) (h2 :: t2) = merge (h1 :: t1) t2
        | Lt => merge (h1 :: t1) (h2 :: t2) = h1 :: merge t1 (h2 :: t2)
        | Gt => merge (h1 :: t1) (h2 :: t2) = h2 :: merge (h1 :: t1) t2
        end.
    Proof.
      apply merge''_cons.
    Qed.

    (** No string matches the empty language. *)
    Lemma MNil : forall z,
        not (exp_match z EmptySet).
    Proof.
      intros. intros C. inv C.
    Qed.

    (** Merging the empty list on the left is the identity. *)
    Lemma merge_nil1 : forall es,
        merge [] es = es.
    Proof. auto. Qed.

    (** Merging the empty list on the right is the identity. *)
    Lemma merge_nil2 : forall es,
        merge es [] = es.
    Proof. destruct es; auto. Qed.


    (** Membership in [merge es es'] iff membership in [es] or [es']; proved by structural induction using [merge_cons]. *)
    Lemma merge_In : forall es es' e,
        In e (merge es es') <-> (In e es \/ In e es').
    Proof.
      intros. split; intros.
      {
        generalize dependent es'. generalize dependent e.
        induction es; intros.
        - rewrite merge_nil1 in H. auto.
        - induction es'; sis; auto.
          assert(L := merge_cons es es' a a0). destruct (re_compare a a0).
          + rewrite L in H. apply IHes' in H. destruct H; auto.
          + rewrite L in H. simpl in H. destruct H; auto.
            apply IHes in H. destruct H; auto.
          + rewrite L in H. simpl in H. destruct H; auto.
            apply IHes' in H. destruct H; auto.
      }
      {
        generalize dependent es'. generalize dependent e.
        induction es; intros.
        - rewrite merge_nil1. destruct H; auto. contradiction.
        - induction es'; sis.
          + destruct H; auto. contradiction.
          + assert(L := merge_cons es es' a a0). destruct (re_compare a a0) eqn:E.
            * rewrite L. apply IHes'. destruct H; auto. destruct H; auto.
              left. left. apply re_compare_eq in E. rewrite E. auto.
            * rewrite L. simpl. destruct H; auto. destruct H; auto.
            * rewrite L. simpl. destruct H; auto. destruct H; auto.
      }
    Qed.

    (* Assume all App inputs and subterms are recursively right associated *)
    (** Flattens a right-recursive iterated application into a list of its factors. *)
    Fixpoint mkIterApp' (e : regex) : list regex :=
      match e with
      | App e1 e2 => e1 :: (mkIterApp' e2)
      | _ => [e]
      end.

    (* Instead of checking for similarity,
       force all regexes to be in the right hand form of the relation.
       Also use associativity/commutativity to force lexical ordering on Unioned exps
       Then check for equality.
     *)
    (** Reduces a regex to a canonical form: right-associated, sorted, duplicate-free unions and apps, with EmptySet/EmptyStr identities applied. *)
    Fixpoint canon (e : regex) : regex :=
      match e with
      | Union e1 e2 =>
        match canon e1, canon e2 with
        (* The next two patters ensure that unions don't contain EmptySet *)
        | EmptySet, ec2 => ec2
        | ec1, EmptySet => ec1
        | ec1, ec2 =>
          (* sort and make right recursive *)
          (* Note : merge also removes duplicates *)
          IterUnion (merge (mkIterUnion' ec1) (mkIterUnion' ec2))
        end
      | App e1 e2 =>
        match canon e1, canon e2 with
        (* The next two patterns ensure that all iterated apps
           containing an EmptySet reduce to the EmptySet *)
        | EmptySet, _ => EmptySet
        | _, EmptySet => EmptySet
        (* The next two patters ensure that apps don't contain EmptyStr *)
        | EmptyStr, ec2 => ec2
        | ec1, EmptyStr => ec1
        | ec1, ec2 =>
          IterApp ( (mkIterApp' ec1) ++ (mkIterApp' ec2) )
        end
      | Star EmptySet => EmptyStr
      | Star EmptyStr => EmptyStr
      (*
      | Star r =>
        match canon r with
        | Star _ => r
        | r' => Star r'
        end*)
      | _ => e
      end.


    (** Matching against [IterApp (mkIterApp' e)] is equivalent to matching against [e]; proved by induction on [e]. *)
    Lemma invertIterApp : forall e z,
        exp_match z (IterApp (mkIterApp' e)) <-> exp_match z e.
    Proof.
      induction e; try(sis; reflexivity).
      sis. dm; try(destruct e2; discriminate).
      rewrite <- E in *. clear E.
      split; intros.
      - inv H. apply IHe2 in H4. constructor; auto.
      - inv H. constructor; auto. apply IHe2. auto.
    Qed.

    (** Matching against [IterApp (e :: es)] is equivalent to matching against [App e (IterApp es)]. *)
    Lemma consIterApp : forall es e z,
        exp_match z (IterApp (e :: es))
        <-> exp_match z (App e (IterApp es)).
    Proof.
      intros. simpl. destruct es.
      {
        split; intros.
        - sis. assert(z = z ++ []). symmetry. apply app_nil_r.
          rewrite H0. clear H0.
          constructor; auto; constructor.
        - inv H. inv H4. rewrite app_nil_r. auto.
      }
      {
        split; intros; auto.
      }
    Qed.

    (** Matching against [IterApp (es ++ es')] is equivalent to matching against [App (IterApp es) (IterApp es')]. *)
    Lemma bar : forall es es' z,
        exp_match z (IterApp (es ++ es'))
        <-> exp_match z (App (IterApp es) (IterApp es')).
    Proof.
      induction es; intros.
      {
        split; intros; sis; assert(z = [] ++ z); auto.
        - rewrite H0. constructor; auto; constructor.
        - inv H. inv H4. sis. auto.
      }
      {
        split; intros.
        - rewrite <- app_comm_cons in H. apply consIterApp in H. inv H.
          apply IHes in H4. inv H4. rewrite app_assoc. constructor; auto.
          apply consIterApp. constructor; auto.
        - remember (a :: es) as es0. inversion H. rewrite Heqes0 in *. clear H1 H2 H0 re1 re2.
          apply consIterApp in H3. inv H3.
          rewrite <- app_comm_cons. rewrite consIterApp. rewrite <- app_assoc.
          constructor; auto. apply IHes. constructor; auto.
      }
    Qed.

    (** Matching against [IterApp (es ++ [e'])] is equivalent to matching against [App (IterApp es) e']. *)
    Lemma foo : forall es z e',
        exp_match z (IterApp (es ++ [e']))
        <-> exp_match z (App (IterApp es) e').
    Proof. intros. apply bar. Qed.


    (** Matching against [IterUnion (mkIterUnion' e)] is equivalent to matching against [e]; proved by induction on [e]. *)
    Lemma invertIterUnion : forall e z,
        exp_match z (IterUnion (mkIterUnion' e)) <-> exp_match z e.
    Proof.
      induction e; try(sis; reflexivity).
      sis. dm; try(destruct e2; discriminate).
      rewrite <- E in *. clear E.
      split; intros.
      - inv H.
        + apply MUnionL. auto.
        + apply IHe2 in H1. apply MUnionR. auto.
      - inv H.
        + constructor; auto.
        + apply MUnionR. apply IHe2. auto.
    Qed.

    (** Matching against [IterUnion (e :: es)] is equivalent to matching against [Union e (IterUnion es)]. *)
    Lemma consIterUnion : forall es e z,
        exp_match z (IterUnion (e :: es))
        <-> exp_match z (Union e (IterUnion es)).
    Proof.
      intros; simpl; destruct es.
      - simpl. split; intros.
        + constructor. auto.
        + inv H; auto. inv H1.
      - split; auto.
    Qed.

    (** A string matches [IterUnion es] iff some element of [es] matches it. *)
    Lemma IterUnion_In_match : forall es z,
      exp_match z (IterUnion es)
      <-> (exists e, In e es /\ exp_match z e).
    Proof.
      induction es; intros.
      {
        split; intros.
        - simpl in H. inv H.
        - destruct H. destruct H. contradiction.
      }
      {
        split; intros.
        - apply consIterUnion in H. inv H.
          + exists a. split; auto. simpl. left. auto.
          + apply IHes in H1. destruct H1. destruct H. exists x. split.
            * simpl. right. auto.
            * auto.
        - apply consIterUnion. destruct H. destruct H. destruct (regex_eq a x) eqn:E.
          + apply regex_eq_correct in E. subst. constructor. auto.
          + destruct H.
            * apply false_not_true in E. destruct E. apply regex_eq_correct. auto.
            * apply MUnionR. apply IHes. eexists; eauto.
      }
    Qed.


    (** Two iterated unions with the same member sets are language-equivalent. *)
    Lemma eq_set_eq_U : forall es es',
        (forall e, In e es <-> In e es')
        -> re_equiv (IterUnion es) (IterUnion es').
    Proof.
      unfold re_equiv. intros. split; intros.
      - rewrite IterUnion_In_match in *. destruct H0. destruct H0.
        apply H in H0. eexists; eauto.
      - rewrite IterUnion_In_match in *. destruct H0. destruct H0.
        apply H in H0. eexists; eauto.
    Qed.

    (** The member set of [merge (a :: es) es'] equals the member set of [a :: merge es es']. *)
    Lemma remove_head : forall es es' z a,
      exp_match z (IterUnion (merge (a :: es) es'))
      <-> exp_match z (IterUnion (a :: (merge es es'))).
    Proof.
      intros. assert(L := eq_set_eq_U). unfold re_equiv in *. apply L. clear L.
      intros. split; intros.
      - sis. rewrite merge_In in *. sis. rewrite <- or_assoc. auto.
      - sis. rewrite merge_In in *. sis. rewrite or_assoc. auto.
    Qed.

    (** Matching against [IterUnion (merge es es')] is equivalent to matching against [IterUnion (es ++ es')]. *)
    Lemma barU : forall es es' z,
        exp_match z (IterUnion (merge es es'))
        <-> exp_match z (IterUnion (es ++ es')).
    Proof.
      induction es; intros.
      {
        assert([] ++ es' = es').
        { auto. }
        split; intros.
        - rewrite H in *; destruct es'; auto.
        - rewrite H in *; destruct es'; auto.
      }
      {
        split; intros.
        - rewrite <- app_comm_cons. rewrite consIterUnion. apply remove_head in H.
          rewrite consIterUnion in H. inv H.
          + constructor; auto.
          + apply MUnionR. apply IHes. auto.
        - rewrite <- app_comm_cons in *. rewrite consIterUnion in *. apply remove_head.
          rewrite consIterUnion. inv H.
          + constructor. auto.
          + apply MUnionR. apply IHes. auto.
      }
    Qed.

    (** Matching against [IterUnion (es ++ es')] is equivalent to matching against [Union (IterUnion es) (IterUnion es')]. *)
    Lemma barU' : forall es es' z,
        exp_match z (IterUnion (es ++ es'))
        <-> exp_match z (Union (IterUnion es) (IterUnion es')).
    Proof.
      induction es; intros.
      {
        split; intros; sis.
        - apply MUnionR. auto.
        - inv H; auto. inv H2.
      }
      {
        split; intros.
        - rewrite <- app_comm_cons in H. apply consIterUnion in H. inv H.
          + apply MUnionL. apply consIterUnion. apply MUnionL. auto.
          + apply IHes in H1. inv H1.
            * apply MUnionL. apply consIterUnion. apply MUnionR. auto.
            * apply MUnionR. auto.
        - rewrite <- app_comm_cons. apply consIterUnion. remember (a :: es) as es0.
          inv H.
          + apply consIterUnion in H2. inv H2.
            * apply MUnionL. auto.
            * apply MUnionR. apply IHes. apply MUnionL. auto.
          + apply MUnionR. apply IHes. apply MUnionR. auto.
      }
    Qed.

    (** Matching against [IterUnion (es ++ [e'])] is equivalent to matching against [Union (IterUnion es) e']. *)
    Lemma fooU : forall es z e',
        exp_match z (IterUnion (es ++ [e']))
        <-> exp_match z (Union (IterUnion es) e').
    Proof. intros. apply barU'. Qed.


    (** Matching [canon (App e1 e2)] implies matching [App e1 e2], assuming IH for each sub-expression. *)
    Lemma canon_App_F : forall z e1 e2,
        exp_match z (canon (App e1 e2))
        -> (forall z : String, exp_match z (canon e1) <-> exp_match z e1)
        -> (forall z : String, exp_match z (canon e2) <-> exp_match z e2)
        -> exp_match z (App e1 e2).
    Proof.
      intros z e1 e2 H IHe1 IHe2.
      simpl in H.
        repeat dm; try(inv H; reflexivity);
          assert(z = [] ++ z); assert(z = z ++ []);
            try(auto; reflexivity); try(rewrite app_nil_r; auto);
              try(rewrite H0; constructor; [apply IHe1; constructor|];
                  apply IHe2; auto; reflexivity);
              try(rewrite H1; constructor; [apply IHe1; auto|];
                  apply IHe2; constructor; reflexivity); clear H0 H1;
                try(inv H; constructor; [apply IHe1; auto|]; apply IHe2; auto; reflexivity);
                try(destruct r2; discriminate);
                try(destruct r4; discriminate);
                try(destruct r0_2; discriminate);
                try(rewrite <- E1 in H; inv H; rewrite foo in H4; inv H4;
                    rewrite invertIterApp in H0; rewrite app_assoc; constructor;
                    [apply IHe1; constructor; auto | apply IHe2; auto]).
        + rewrite <- E1 in H. inv H. constructor; [apply IHe1; auto|].
          inv H4. apply IHe2. constructor; auto. rewrite invertIterApp in H5. auto.
        + rewrite <- E1 in H. inv H. rewrite bar in H4. inv H4. dm.
          * rewrite invertIterApp in H0. rewrite app_assoc. constructor.
            -- apply IHe1. constructor; auto.
            -- destruct r4; try(discriminate).
          * rewrite <- E2 in H5. inv H5. rewrite invertIterApp in *. rewrite app_assoc.
            constructor; [apply IHe1|apply IHe2]; constructor; auto.
        + rewrite <- E1 in H. inv H. inv H4. rewrite invertIterApp in *.
          constructor; [apply IHe1; auto|]. apply IHe2. constructor; auto.
        + rewrite <- E1 in H. inv H. inv H4. rewrite invertIterApp in *.
          constructor; [apply IHe1; auto|]. apply IHe2. constructor; auto.
    Qed.

    (** Language equivalence is preserved by the [Star] constructor. *)
    Lemma eq_Star : forall e1 e2,
        re_equiv e1 e2
        -> re_equiv (Star e1) (Star e2).
    Proof.
      intros. unfold re_equiv in *. intros. split; intros.
      - apply star_concat in H0. destruct H0 as (xss & H1 & H0).
        rewrite H1. clear H1. apply concat_star. intros.
        apply H. apply H0. auto.
      - apply star_concat in H0. destruct H0 as (xss & H1 & H0).
        rewrite H1. clear H1. apply concat_star. intros.
        apply H. apply H0. auto.
    Qed.

    (** Matching [canon (Star e)] is equivalent to matching [Star (canon e)], using [eq_Star]. *)
    Lemma canon_Star : forall z e,
        (forall z : String, exp_match z (canon e) <-> exp_match z e)
        -> (exp_match z (canon (Star e))
        <-> exp_match z (Star (canon e))).
    Proof.
      intros. split; intros; sis.
      - dm.
        + inv H0. constructor.
        + inv H0. constructor.
        + assert (L := eq_Star (App r1 r2) (canon (App r1 r2))).
          unfold re_equiv in *. symmetry in H. eapply L in H. apply H. auto.
        + assert (L := eq_Star (Union r1 r2) (canon (Union r1 r2))).
          unfold re_equiv in *. symmetry in H. eapply L in H. apply H. auto.
        + assert (L := eq_Star (Star r) (canon (Star r))).
          unfold re_equiv in *. symmetry in H. eapply L in H. apply H. auto.
      - dm.
        + sis. inv H0; try constructor. inv H2.
        + apply star_concat in H0. destruct H0 as (xss & H1 & H0).
          assert(forall xs, In xs xss -> xs = []).
          { intros. apply H0 in H2. rewrite H in H2. inv H2. auto. }
          assert(z = []).
          { clear H H0. induction xss.
            - sis. auto.
            - sis.
              assert (a = []).
              { apply H2. auto. }
              subst. sis. apply IHxss; auto.
          }
          rewrite H3. constructor.
        + assert (L := eq_Star (App r1 r2) (canon (App r1 r2))). unfold re_equiv in *.
          symmetry in H. eapply L in H. apply H. auto.
        + assert (L := eq_Star (Union r1 r2) (canon (Union r1 r2))). unfold re_equiv in *.
          symmetry in H. eapply L in H. apply H. auto.
        + assert (L := eq_Star (Star r) (canon (Star r))). unfold re_equiv in *.
          symmetry in H. eapply L in H. apply H. auto.
    Qed.

    (** [canon e] is language-equivalent to [e] for all regexes; proved by structural induction with case analyses. *)
    Lemma canon_equiv : forall e,
        re_equiv (canon e) e.
    Proof.
      induction e; unfold re_equiv in *; split; intros; try(sis; auto; discriminate).
      - apply canon_App_F; auto.
      - simpl.
        repeat dm; try(inv H; reflexivity);
          assert(z = [] ++ z); assert(z = z ++ []);
            try(auto; reflexivity); try(rewrite app_nil_r; auto);
              try(rewrite H0 in H; inv H; rewrite <- IHe1 in *; inv H5; reflexivity);
              try(rewrite H1 in H; inv H; rewrite <- IHe2 in *; inv H6; reflexivity);
              try(inv H; rewrite <- IHe1 in *; rewrite <- IHe2 in *;
                  constructor; auto; reflexivity);
              try(inv H; rewrite <- IHe1 in *; rewrite <- IHe2 in *;
                  inv H5; inv H6; simpl; constructor; auto; reflexivity);
              try(destruct r2; discriminate);
              try(rewrite <- E1; inv H; rewrite <- IHe1 in *; rewrite <- IHe2 in *;
                  inv H5; inv H6; repeat constructor; auto; rewrite invertIterApp; auto);
              try(inv H; rewrite <- IHe1 in *; rewrite <- IHe2 in *;
                  inv H5; inv H6; repeat rewrite app_nil_r; repeat constructor; auto; reflexivity);
              try(rewrite <- E1; inv H; rewrite <- IHe1 in *; rewrite <- IHe2 in *;
                  inv H5; rewrite <- app_assoc; constructor; auto;
                  rewrite bar; constructor; [rewrite invertIterApp|]; auto);
              try(destruct r4; discriminate);
              try(destruct r0_2; discriminate).
        + simpl. dm; try(destruct r4; discriminate).
          inv H6. constructor; auto. rewrite <-  E2. apply invertIterApp. auto.

      - simpl in H.
        repeat dm; repeat dm; try(inv H; reflexivity);
          try(apply MUnionR; rewrite <- IHe2; auto; reflexivity);
          try(apply MUnionL; rewrite <- IHe1; auto; reflexivity);
          try(inv H; [apply MUnionL; rewrite <- IHe1; auto
                     |apply MUnionR; rewrite <- IHe2; auto]; reflexivity);
          try(inv H; [apply MUnionR; rewrite <- IHe2; auto
                     |apply MUnionL; rewrite <- IHe1; auto]; reflexivity);
          try(rewrite barU in H; simpl in H; dm; try(destruct r2; discriminate);
              rewrite <- E1 in H; inv H; [apply MUnionL; rewrite <- IHe1; auto|];
              apply MUnionR; rewrite <- IHe2; inv H1; [apply MUnionL; auto|];
              apply MUnionR; rewrite invertIterUnion in *; auto);
          try(rewrite barU in H; simpl in H; inv H;
              [apply MUnionL; rewrite <- IHe1; auto
              |apply MUnionR; rewrite <- IHe2; auto]; reflexivity).
        + rewrite barU in H; simpl in H; inv H;
              [apply MUnionL; rewrite <- IHe1; auto
              |apply MUnionR; rewrite <- IHe2; auto].
          dm; try(destruct r4; discriminate).
          rewrite <- E1 in *. inv H1; [apply MUnionL; auto|rewrite invertIterUnion in H0].
          apply MUnionR; auto.
        + rewrite barU in H. rewrite fooU in H. inv H;
              [apply MUnionL; rewrite <- IHe1; auto
              |apply MUnionR; rewrite <- IHe2; auto].
          dm; [destruct r2; discriminate|]. rewrite <- E1 in H2.
          inv H2. apply MUnionL. auto.
          apply MUnionR. rewrite invertIterUnion in H1. auto.
        + rewrite barU in H. rewrite fooU in H. inv H;
              [apply MUnionL; rewrite <- IHe1; auto
              |apply MUnionR; rewrite <- IHe2; auto].
          dm; [destruct r2; discriminate|]. rewrite <- E1 in H2.
          inv H2. apply MUnionL. auto.
          apply MUnionR. rewrite invertIterUnion in H1. auto.
        + rewrite barU in H. rewrite fooU in H. inv H;
              [apply MUnionL; rewrite <- IHe1; auto
              |apply MUnionR; rewrite <- IHe2; auto].
          dm; [destruct r2; discriminate|]. rewrite <- E1 in H2.
          inv H2. apply MUnionL. auto.
          apply MUnionR. rewrite invertIterUnion in H1. auto.
        + rewrite barU in H. rewrite barU' in H.
          inv H; dm; try(destruct r2; destruct r4; discriminate).
          * apply MUnionL. rewrite <- IHe1. rewrite <- E1 in H2. inv H2.
            apply MUnionL; auto. rewrite invertIterUnion in *. apply MUnionR. auto.
          * apply MUnionR. rewrite <- IHe2. rewrite <- E1 in H1. inv H1.
            apply MUnionL; auto. rewrite invertIterUnion in *. apply MUnionR. auto.
        + rewrite barU in H. rewrite barU' in H.
          inv H; [dm|]; try(destruct r2; discriminate).
          * apply MUnionL. rewrite <- IHe1. rewrite <- E1 in H2. inv H2.
            apply MUnionL. auto. apply MUnionR. rewrite invertIterUnion in *. auto.
          * apply MUnionR. rewrite <- IHe2. auto.
        + rewrite barU in H. rewrite barU' in H. inv H.
          * rewrite IHe1 in *. apply MUnionL. auto.
          * dm; try(destruct r0_2; discriminate). rewrite <- E1 in *.
            apply MUnionR. apply IHe2. inv H1.
            -- apply MUnionL. auto.
            -- apply MUnionR. rewrite invertIterUnion in *. auto.
      - simpl.
        repeat dm; try(inv H; reflexivity);
          try(rewrite barU; simpl);
          try(inv H; [rewrite <- IHe1 in *; inv H2 | rewrite <- IHe2 in *; auto]; reflexivity);
          try(inv H; [rewrite <- IHe1 in *; auto | rewrite <- IHe2 in *; inv H1]; reflexivity);
          try(inv H; [rewrite <- IHe1 in *; auto | rewrite <- IHe2 in *; auto]; reflexivity);
          try(inv H; [rewrite <- IHe1 in *; apply MUnionL; auto
                     | rewrite <- IHe2 in *; apply MUnionR; auto]; reflexivity);
          try(inv H; [rewrite <- IHe1 in *; apply MUnionR; auto
                     | rewrite <- IHe2 in *; apply MUnionL; auto]; reflexivity);
          dm; try(destruct r4; discriminate); try(destruct r2; discriminate);
            try(destruct r0_2; discriminate); try(rewrite <- E1; clear E1);
              try(inv H; [rewrite <- IHe1 in * | rewrite <- IHe2 in *]);
              try(apply MUnionL; auto; reflexivity);
              try(inv H1);
              try(apply MUnionL; auto; reflexivity);
              try(apply MUnionR; apply MUnionL; auto; reflexivity);
              try(apply MUnionR; apply MUnionR; rewrite invertIterUnion; auto; reflexivity);
              try(inv H2; [apply MUnionL; auto; reflexivity|];
                  apply MUnionR; apply barU'; apply MUnionL; apply invertIterUnion; auto);
              try(apply MUnionR; apply barU'; apply MUnionR; simpl; constructor); auto.
        + apply MUnionR. apply barU'. apply MUnionR. simpl.
          dm; try(discriminate). apply MUnionL. auto.
        + apply MUnionR. apply barU'. apply MUnionR. simpl.
          dm; try(destruct r4; discriminate). apply MUnionR. rewrite <- E1.
          apply invertIterUnion. auto.
      - rewrite canon_Star in H; auto. apply star_concat in H.
        destruct H as (xss & H). destruct H.
        rewrite H in *. apply concat_star. intros. apply IHe. apply H0. auto.
      - apply canon_Star; auto. apply star_concat in H. destruct H as (xss & H). destruct H.
        rewrite H in *. apply concat_star. intros. apply IHe. apply H0. auto.
    Qed.

    (** Fills the transition table for [e] over alphabet [bs] using nat-indexed fuel; inner helper for the main filler. *)
    Fixpoint fill_Table_all'' (T : Table) (e : regex) (bs : list Sigma) (fuel : nat) : Table :=
      match fuel with
      | 0 => T
      | S n =>
        let
          (* We need a helper function to apply fill_Table_all to each derivative of e *)
          fix fill_Table_ds (bs : list Sigma) (bs' : list Sigma) :=
          match bs' with
          | [] => T
          | c :: cs =>
            let
              (* fill the table with respect to the tail *)
              T1 := fill_Table_ds bs cs in
            let
              (* now we'll do it with respect to c *)
              d := canon (derivative c e) in
            match get_eq T1 d with
            | None =>
              let
                (* we didn't find a similar regex, we need to add d *)
                T2 := add_state T1 d in
              let
                (* we also need to transition from regex e to regex d on symbol c *)
                T3 := set_Table T2 e c d in
              (* finally we need to fill up the table with respect to d *)
              fill_Table_all'' T3 d bs n
            | Some e' =>
              (* In this case, we found a regex that has already been added to the table *)
              (* Anytime we add a regex, we immediately call fill_Table_all for it *)
              (* Therefore, we don't need to call fill_Table_all again *)
              (* Instead, we transition from e to e' when we see c *)
              set_Table T1 e c e'
            end
          end
        in
        fill_Table_ds bs bs
      end.

    (** Fills the transition table for [e] over alphabet [bs] with nat-indexed fuel; the canonical table builder variant. *)
    Fixpoint fill_Table_all' (T : Table) (e : regex) (bs : list Sigma) (fuel : nat) : Table :=
      match fuel with
      | 0 => T
      | S n =>
        let
          (* We need a helper function to apply fill_Table_all to each derivative of e *)
          fix fill_Table_ds (bs' : list Sigma) :=
          match bs' with
          | [] => T
          | c :: cs =>
            let
              (* fill the table with respect to the tail *)
              T1 := fill_Table_ds cs in
            let
              (* now we'll do it with respect to c *)
              d := canon (derivative c e) in
            match get_eq T1 d with
            | None =>
              let
                (* we didn't find a similar regex, we need to add d *)
                T2 := add_state T1 d in
              let
                (* we also need to transition from regex e to regex d on symbol c *)
                T3 := set_Table T2 e c d in
              (* finally we need to fill up the table with respect to d *)
              fill_Table_all' T3 d bs n
            | Some e' =>
              (* In this case, we found a regex that has already been added to the table *)
              (* Anytime we add a regex, we immediately call fill_Table_all for it *)
              (* Therefore, we don't need to call fill_Table_all again *)
              (* Instead, we transition from e to e' when we see c *)
              set_Table T1 e c e'
            end
          end
        in
        fill_Table_ds bs
      end.

    (** Fills the transition table starting from the canonical form of [e]; wraps [fill_Table_all']. *)
    Definition fill_Table_all (T : Table) (e : regex) (bs : list Sigma) (fuel : nat) : Table :=
      fill_Table_all' T (canon e) bs fuel.

    (** Accessibility lemma: the predecessor of a non-unit positive is accessible under [Pos.to_nat] ordering. *)
    Lemma acc_rec_call' : forall fuel,
        Acc (ltof positive Pos.to_nat) fuel
        -> fuel <> xH
        -> Acc (ltof positive Pos.to_nat) (Pos.pred fuel).
    Proof.
      intros. apply Acc_inv with (x := fuel); auto.
      assert((1 < fuel)%positive).
      { clear H. destruct fuel; try constructor; try contradiction. }
      clear H0 H. apply Pos2Nat.inj_lt.
      apply Pos2Nat.inj_pred in H1. apply Pos2Nat.inj_lt. rewrite H1.
      apply Nat.lt_pred_l. pose proof Pos2Nat.is_pos fuel. lia.
    Defined.

    (** Accessibility of [Pos.pred fuel] when [fuel] has the form [p~1]. *)
    Lemma acc_rec_call_xI : forall fuel p,
        Acc (ltof positive Pos.to_nat) fuel
        -> fuel = (p~1)%positive
        -> Acc (ltof positive Pos.to_nat) (Pos.pred fuel).
    Proof.
      intros. apply acc_rec_call'; auto. intros C. rewrite C in H0. discriminate.
    Defined.

    (** Accessibility of [Pos.pred fuel] when [fuel] has the form [p~0]. *)
    Lemma acc_rec_call_xO : forall fuel p,
        Acc (ltof positive Pos.to_nat) fuel
        -> fuel = (p~0)%positive
        -> Acc (ltof positive Pos.to_nat) (Pos.pred fuel).
    Proof.
      intros. apply acc_rec_call'; auto. intros C. rewrite C in H0. discriminate.
    Defined.

    (** Accessibility of [Pos.pred xH]; trivial since [Pos.pred xH = xH]. *)
    Lemma acc_rec_call_xH : forall fuel,
        Acc (ltof positive Pos.to_nat) fuel
        -> fuel = xH
        -> Acc (ltof positive Pos.to_nat) (Pos.pred fuel).
    Proof.
      intros. rewrite H0 in *. sis. auto.
    Defined.

    (** Every positive is accessible under the [Pos.to_nat] well-founded ordering. *)
    Lemma Poslt_wf : forall p, Acc (ltof positive Pos.to_nat) p.
    Proof.
      pose proof well_founded_ltof positive Pos.to_nat. unfold well_founded in H. auto.
    Qed.

    (** Example traversal that counts down a positive integer to xH using its accessibility; used as a proof-of-concept. *)
    Fixpoint traverse_pos' (fuel : positive)
             (Ha : Acc (ltof positive Pos.to_nat) fuel)
             {struct Ha} : positive :=
      match fuel as fuel'
            return fuel = fuel' -> _
      with
      | xH => fun Heq => xH
      | xI p => fun Heq => traverse_pos' (Pos.pred fuel) (acc_rec_call_xI fuel p Ha Heq)
      | xO p => fun Heq => traverse_pos' (Pos.pred fuel) (acc_rec_call_xO fuel p Ha Heq)
      end eq_refl.

    (** Top-level wrapper for [traverse_pos']; supplies the [Poslt_wf] accessibility term. *)
    Definition traverse_pos (fuel : positive) : positive :=
      traverse_pos' fuel (Poslt_wf _).

    (** Fills the transition table using binary positive fuel and an explicit accessibility witness; terminates structurally on [Ha]. *)
    Fixpoint fill_Table_all'_bin (T : Table) (e : regex) (bs : list Sigma) (fuel : positive)
             (Ha : Acc (ltof positive Pos.to_nat) fuel) {struct Ha} : Table :=
      match fuel as fuel'
            return fuel = fuel' -> _
      with
      | xH => fun _ => T
      | xI p =>
        fun Heq =>
          let
            (* We need a helper function to apply fill_Table_all to each derivative of e *)
            fix fill_Table_ds_bin (bs' : list Sigma) :=
            match bs' with
            | [] => T
            | c :: cs =>
              let
                (* fill the table with respect to the tail *)
                T1 := fill_Table_ds_bin cs in
              let
                (* now we'll do it with respect to c *)
                d := canon (derivative c e) in
              match get_eq T1 d with
              | None =>
                let
                  (* we didn't find a similar regex, we need to add d *)
                  T2 := add_state T1 d in
                let
                  (* we also need to transition from regex e to regex d on symbol c *)
                  T3 := set_Table T2 e c d in
                (* finally we need to fill up the table with respect to d *)
                fill_Table_all'_bin T3 d bs (Pos.pred fuel) (acc_rec_call_xI fuel p Ha Heq)
              | Some e' =>
                (* In this case, we found a regex that has already been added to the table *)
                (* Anytime we add a regex, we immediately call fill_Table_all for it *)
                (* Therefore, we don't need to call fill_Table_all again *)
                (* Instead, we transition from e to e' when we see c *)
                set_Table T1 e c e'
              end
            end
          in
          fill_Table_ds_bin bs
      | xO p =>
        fun Heq =>
          let
            (* We need a helper function to apply fill_Table_all to each derivative of e *)
            fix fill_Table_ds_bin (bs' : list Sigma) :=
            match bs' with
            | [] => T
            | c :: cs =>
              let
                (* fill the table with respect to the tail *)
                T1 := fill_Table_ds_bin cs in
              let
                (* now we'll do it with respect to c *)
                d := canon (derivative c e) in
              match get_eq T1 d with
              | None =>
                let
                  (* we didn't find a similar regex, we need to add d *)
                  T2 := add_state T1 d in
                let
                  (* we also need to transition from regex e to regex d on symbol c *)
                  T3 := set_Table T2 e c d in
                (* finally we need to fill up the table with respect to d *)
                fill_Table_all'_bin T3 d bs (Pos.pred fuel) (acc_rec_call_xO fuel p Ha Heq)
              | Some e' =>
                (* In this case, we found a regex that has already been added to the table *)
                (* Anytime we add a regex, we immediately call fill_Table_all for it *)
                (* Therefore, we don't need to call fill_Table_all again *)
                (* Instead, we transition from e to e' when we see c *)
                set_Table T1 e c e'
              end
            end
          in
          fill_Table_ds_bin bs
      end eq_refl.

    (** Top-level binary-fuel table filler; applies [canon] to [e] then calls [fill_Table_all'_bin] with [Poslt_wf]. *)
    Definition fill_Table_all_bin (T : Table) (e : regex) (bs : list Sigma)
               (fuel : positive) : Table :=
      fill_Table_all'_bin T (canon e) bs fuel (Poslt_wf _).

  End FillTable.

  (** The [derived] invariant: every table entry is language-equivalent to the corresponding Brzozowski derivative. *)
  Module Export Spec.

    (** Invariant asserting that every table entry [r] at [(e, a)] is language-equivalent to [derivative a e]. *)
    Definition derived (T : Table) : Prop :=
      forall e a r, get_Table T e a = Some r -> re_equiv r (derivative a e).

  End Spec.

  (** Proofs that the empty table and table-filling operations preserve the [derived] invariant. *)
  Module Export Correct.

    (** The empty table vacuously satisfies [derived] since it has no entries. *)
    Theorem emptyTable_derived : derived emptyTable.
    Proof.
      unfold derived. intros. rewrite correct_emptyTable in H. discriminate.
    Qed.

    (** Unfolds one step of [fill_Table_all'] at a successor fuel value. *)
    Lemma unfold_filler' : forall bs T e n,
        fill_Table_all' T e bs (S n)
        =
        let
          fix fill_Table_ds (bs' : list Sigma) : Table :=
          match bs' with
          | [] => T
          | c :: cs =>
            let T1 := fill_Table_ds cs in
            let d := canon (derivative c e) in
            match get_eq T1 d with
            | Some e' => set_Table T1 e c e'
            | None =>
              let T2 := add_state T1 d in
              let T3 := set_Table T2 e c d in fill_Table_all' T3 d bs n
            end
          end in
        fill_Table_ds bs.
    Proof.
      auto.
    Qed.

    (** Case-splits the inner derivative-filling loop on the head symbol, exposing either a [set_Table] or a recursive fill. *)
    Lemma unfold_filler_ds : forall T T' e x xs n,
        let
          fix fill_Table_ds (bs' : list Sigma) : Table :=
          match bs' with
          | [] => T
          | c :: cs =>
            let T1 := fill_Table_ds cs in
            let d := canon (derivative c e) in
            match get_eq T1 d with
            | Some e' => set_Table T1 e c e'
            | None =>
              let T2 := add_state T1 d in
              let T3 := set_Table T2 e c d in fill_Table_all' T3 d (x :: xs) n
            end
          end in
        T' = fill_Table_ds (x :: xs)
        ->
        (exists e' T0, get_eq (fill_Table_ds xs) (canon (derivative x e)) = Some e'
                  /\ T0 = (fill_Table_ds xs)
                  /\ T' = set_Table T0 e x e')
        \/
        (exists T0, get_eq (fill_Table_ds xs) (canon (derivative x e)) = None
               /\
               T0 = (fill_Table_ds xs)
               /\
               T' = fill_Table_all'
                      (set_Table (add_state T0 (canon (derivative x e))) e x
                                 (canon (derivative x e)))
                      (canon (derivative x e)) (x :: xs) n).
    Proof.
      intros. simpl in *. destruct (get_eq (fill_Table_ds xs) (canon (derivative x e))) eqn:E.
      - left. eexists; eauto.
      - right. eexists; eauto.
    Qed.

    (** Setting a table entry with a language-equivalent regex preserves [derived]; proved by case split on key equality. *)
    Theorem derived_closure_set : forall T b e r,
        derived T
        -> re_equiv r (derivative b e)
        -> derived (set_Table T e b r).
    Proof.
      intros.
      unfold derived. intros.
      destruct (regex_eq e e0) eqn:E; destruct (Sigma_dec a b).
      - apply regex_eq_correct in E. subst.
        rewrite correct_Table in H1. injection H1; intros; subst.
        auto.
      - rewrite moot_setTable in H1; auto.
      - rewrite moot_setTable in H1; auto.
        assert(regex_eq e e0 <> true).
        { intros C. rewrite C in *. discriminate. }
        right. intros C. destruct H2. apply regex_eq_correct. auto.
      - rewrite moot_setTable in H1; auto.
    Qed.

    (** Adding a state to a derived table yields a derived table; [add_state] does not affect transition entries. *)
    Theorem derived_closure_add : forall T T' e,
        derived T
        -> T' = add_state T e
        -> derived T'.
    Proof.
      unfold derived in *. intros.
      rewrite H0 in H1. rewrite <- moot_add_state with (r:=e) in H1.
      apply H in H1. auto.
    Qed.

    (** The inner derivative-filling loop preserves [derived], assuming the recursive call does; proved by induction on the symbol list. *)
    Lemma derived_closure_ds' : forall bs T T' e n xs,
        (forall (cs : list Sigma) (e : regex) (T T' : Table),
            derived T -> T' = fill_Table_all' T e cs n -> derived T')
        -> derived T
        ->
        let
          fix fill_Table_ds (bs' : list Sigma) : Table :=
          match bs' with
          | [] => T
          | c :: cs =>
            let T1 := fill_Table_ds cs in
            let d := canon (derivative c e) in
            match get_eq T1 d with
            | Some e' => set_Table T1 e c e'
            | None =>
              let T2 := add_state T1 d in
              let T3 := set_Table T2 e c d in fill_Table_all' T3 d xs n
            end
          end in
        T' = fill_Table_ds bs
        -> derived T'.
    Proof.
      intros.
      generalize dependent T.
      generalize dependent T'.
      generalize dependent e.
      generalize dependent xs.
      induction bs as [|b bs]; intros.
      - subst; auto.
      - simpl in H1. repeat dm.
        + assert(derived (fill_Table_ds bs)).
          {
            apply IHbs with (T:=T) (e:=e) (xs:=xs); auto.
          }
          apply get_eq_correct in E. destruct E.
          rewrite H1.
          apply derived_closure_set; auto.
          rewrite <- regex_eq_correct in H4. rewrite <- H4.
          apply canon_equiv.
        + assert(derived (fill_Table_ds bs)).
          {
            apply IHbs with (T:=T) (e:=e) (xs:=xs); auto.
          }
          assert(derived (add_state (fill_Table_ds bs) (canon (derivative b e)))).
          {
            eapply derived_closure_add; eauto.
          }
          clear H2.
          assert(derived (set_Table
                            (add_state (fill_Table_ds bs) (canon (derivative b e)))
                            e b (canon (derivative b e)))).
          {
            eapply derived_closure_set; eauto.
            apply canon_equiv.
          }
          eapply H; eauto.
    Qed.

    (** Convenience wrapper: the inner derivative-filling loop on [bs] yields a derived table. *)
    Lemma derived_closure_ds : forall bs T e n xs,
        (forall (cs : list Sigma) (e : regex) (T T' : Table),
            derived T -> T' = fill_Table_all' T e cs n -> derived T')
        -> derived T
        ->
        let
          fix fill_Table_ds (bs' : list Sigma) : Table :=
          match bs' with
          | [] => T
          | c :: cs =>
            let T1 := fill_Table_ds cs in
            let d := canon (derivative c e) in
            match get_eq T1 d with
            | Some e' => set_Table T1 e c e'
            | None =>
              let T2 := add_state T1 d in
              let T3 := set_Table T2 e c d in fill_Table_all' T3 d xs n
            end
          end in
        derived (fill_Table_ds bs).
    Proof.
      intros. apply derived_closure_ds' with (bs:=bs) (T:=T) (e:=e) (n:=n) (xs:=xs); auto.
    Qed.


    (** [fill_Table_all'] preserves [derived] for any fuel; proved by induction on [n]. *)
    Theorem derived_closure_all' : forall n bs e T T',
        derived T
        -> T' = fill_Table_all' T e bs n
        -> derived T'.
    Proof.
      induction n; intros; try(simpl in H0; subst; auto; reflexivity).
      destruct bs as [|b bs].
      - simpl in H0. subst. auto.
      - rewrite unfold_filler' in H0. apply unfold_filler_ds in H0. destruct H0.
        + destruct H0 as (e' & T0 & H0 & H1 & H2).
          assert(derived T0).
          {
            apply derived_closure_ds with (bs:=bs) (xs:= (b :: bs)) (e:=e) (n:=n) in H.
            subst. auto. apply IHn.
          }
          clear H1.
          subst. eapply derived_closure_set; eauto.
          apply get_eq_correct in H0. destruct H0.
          apply regex_eq_correct in H1. rewrite <- H1.
          apply canon_equiv.
        + destruct H0 as (T0 & H0 & H1 & H2).
          assert(derived T0).
          {
            apply derived_closure_ds with (bs:=bs) (xs:= (b :: bs)) (e:=e) (n:=n) in H.
            subst. auto. apply IHn.
          }
          clear H1.
          assert(derived (add_state T0 (canon (derivative b e)))).
          {
            eapply derived_closure_add; eauto.
          }
          assert(derived (set_Table (add_state T0 (canon (derivative b e)))
                                    e b (canon (derivative b e)))).
          {
            eapply derived_closure_set; eauto.
            apply canon_equiv.
          }
          eapply IHn; eauto.
    Qed.

    (** [fill_Table_all] preserves [derived]; wraps [derived_closure_all']. *)
    Theorem derived_closure_all : forall n bs e T T',
        derived T
        -> T' = fill_Table_all T e bs n
        -> derived T'.
    Proof.
      intros. unfold fill_Table_all in *. eapply derived_closure_all'; eauto.
    Qed.



    (** Any entry retrieved from a derived table is language-equivalent to the corresponding derivative; direct unwrapping of [derived]. *)
    Theorem derived_get_some : forall T e a e',
        derived T
        -> get_Table T e a = Some e'
        -> re_equiv e' (derivative a e).
    Proof.
      intros. unfold derived in *. apply H in H0. auto.
    Qed.

  End Correct.

  (** Proofs relating the binary positive-fuel filler to the nat-fuel filler and showing it also preserves [derived]. *)
  Module Export binary.

    (** Unfolds one step of [fill_Table_all'_bin] by eliminating its [Acc] witness. *)
    Lemma filler_eq_body : forall T e bs fuel Ha,
      fill_Table_all'_bin T e bs fuel Ha
      = match fuel as fuel' return (fuel = fuel' -> Table) with
        | (p~1)%positive =>
          fun Heq : fuel = (p~1)%positive =>
            let
              fix fill_Table_ds (bs' : list Sigma) : Table :=
              match bs' with
              | [] => T
              | c :: cs =>
                let T1 := fill_Table_ds cs in
                let d := canon (derivative c e) in
                match get_eq T1 d with
                | Some e' => set_Table T1 e c e'
                | None =>
                  let T2 := add_state T1 d in
                  let T3 := set_Table T2 e c d in
                  fill_Table_all'_bin T3 d bs (Pos.pred fuel) (acc_rec_call_xI fuel p Ha Heq)
                end
              end in
            fill_Table_ds bs
        | (p~0)%positive =>
          fun Heq : fuel = (p~0)%positive =>
            let
              fix fill_Table_ds (bs' : list Sigma) : Table :=
              match bs' with
              | [] => T
              | c :: cs =>
                let T1 := fill_Table_ds cs in
                let d := canon (derivative c e) in
                match get_eq T1 d with
                | Some e' => set_Table T1 e c e'
                | None =>
                  let T2 := add_state T1 d in
                  let T3 := set_Table T2 e c d in
                  fill_Table_all'_bin T3 d bs (Pos.pred fuel) (acc_rec_call_xO fuel p Ha Heq)
                end
              end in
            fill_Table_ds bs
        | 1%positive => fun _ : fuel = 1%positive => T
        end eq_refl.
    Proof.
      intros. unfold fill_Table_all'_bin. destruct Ha. auto.
    Qed.

    (** [fill_Table_all'_bin] with positive fuel [p] computes the same table as [fill_Table_all'] with nat fuel [pred (Pos.to_nat p)]; proved by induction on the accessibility witness. *)
    Theorem fill_bin'_equiv' : forall (x : positive) (Ha_x : Acc (ltof positive (Pos.to_nat)) x)
                                 (p : positive) (Ha : Acc (ltof positive (Pos.to_nat)) p)
                                 (bs : list Sigma) (T : Table) (e : regex),
        x = p
        -> fill_Table_all'_bin T e bs p Ha = fill_Table_all' T e bs (pred (Pos.to_nat p)).
    Proof.
      intros x Ha_x. induction Ha_x. intros. subst. destruct p eqn:E.
      - destruct (Init.Nat.pred (Pos.to_nat p0~1)) eqn:E1.
        {
          rewrite <- Pos2Nat.inj_pred in E1. 2:{ constructor. }
          pose proof Pos2Nat.is_pos (Pos.pred p0~1). rewrite E1 in H1. lia.
        }
        rewrite unfold_filler'.
        rewrite filler_eq_body. simpl.
        (* Sorry to anyone about to read this massive assert
           -- we just need the inner bs to be more general than the outer bs,
         so we replace it with orig :) *)
        assert(
            exists orig,
              (fix fill_Table_ds (bs' : list Sigma) : Table :=
                 match bs' with
                 | [] => T
                 | c :: cs =>
                   match get_eq (fill_Table_ds cs) (canon (derivative c e)) with
                   | Some e' => set_Table (fill_Table_ds cs) e c e'
                   | None =>
                     fill_Table_all'_bin
                       (set_Table (add_state (fill_Table_ds cs) (canon (derivative c e))) e c
                                  (canon (derivative c e))) (canon (derivative c e)) bs p0~0
                       (acc_rec_call_xI p0~1 p0 Ha eq_refl)
                   end
                 end)
              =  (fix fill_Table_ds (bs' : list Sigma) : Table :=
                    match bs' with
                    | [] => T
                    | c :: cs =>
                      match get_eq (fill_Table_ds cs) (canon (derivative c e)) with
                      | Some e' => set_Table (fill_Table_ds cs) e c e'
                      | None =>
                        fill_Table_all'_bin
                          (set_Table (add_state (fill_Table_ds cs) (canon (derivative c e))) e c
                                     (canon (derivative c e))) (canon (derivative c e)) orig p0~0
                          (acc_rec_call_xI p0~1 p0 Ha eq_refl)
                      end
                    end)
              /\ (fix fill_Table_ds (bs' : list Sigma) : Table :=
                     match bs' with
                     | [] => T
                     | c :: cs =>
                       match get_eq (fill_Table_ds cs) (canon (derivative c e)) with
                       | Some e' => set_Table (fill_Table_ds cs) e c e'
                       | None =>
                         fill_Table_all'
                           (set_Table (add_state (fill_Table_ds cs) (canon (derivative c e))) e c
                                      (canon (derivative c e))) (canon (derivative c e)) bs n
                       end
                     end)
                = (fix fill_Table_ds (bs' : list Sigma) : Table :=
                       match bs' with
                       | [] => T
                       | c :: cs =>
                         match get_eq (fill_Table_ds cs) (canon (derivative c e)) with
                         | Some e' => set_Table (fill_Table_ds cs) e c e'
                         | None =>
                           fill_Table_all'
                             (set_Table (add_state (fill_Table_ds cs) (canon (derivative c e))) e c
                                        (canon (derivative c e))) (canon (derivative c e)) orig n
                         end
                       end)).
        { eauto. }
        destruct H1 as (orig & H1 & H2).
        rewrite H1. rewrite H2. clear H1 H2.
        induction bs; auto.
        rewrite IHbs. dm.
        clear IHbs E0. rewrite H0 with (y := xO p0); auto. clear H0.
        2: { constructor. }
        assert(n = pred (Pos.to_nat p0~0)).
        {
          rewrite <- Pos2Nat.inj_pred in E1.
          2: { constructor. }
          simpl in E1. rewrite E1. lia.
        }
        rewrite H0. auto.
      - destruct (Init.Nat.pred (Pos.to_nat p0~0)) eqn:E1.
        {
          rewrite <- Pos2Nat.inj_pred in E1. 2:{ constructor. }
          pose proof Pos2Nat.is_pos (Pos.pred p0~0). rewrite E1 in H1. lia.
        }
        rewrite unfold_filler'.
        rewrite filler_eq_body. simpl.
        assert(
            exists orig,
              (fix fill_Table_ds (bs' : list Sigma) : Table :=
                 match bs' with
                 | [] => T
                 | c :: cs =>
                   match get_eq (fill_Table_ds cs) (canon (derivative c e)) with
                   | Some e' => set_Table (fill_Table_ds cs) e c e'
                   | None =>
                     fill_Table_all'_bin
                       (set_Table (add_state (fill_Table_ds cs) (canon (derivative c e))) e c
                                  (canon (derivative c e))) (canon (derivative c e)) bs
                       (Pos.pred_double p0) (acc_rec_call_xO p0~0 p0 Ha eq_refl)
                   end
                 end)
              = (fix fill_Table_ds (bs' : list Sigma) : Table :=
                   match bs' with
                   | [] => T
                   | c :: cs =>
                     match get_eq (fill_Table_ds cs) (canon (derivative c e)) with
                     | Some e' => set_Table (fill_Table_ds cs) e c e'
                     | None =>
                       fill_Table_all'_bin
                         (set_Table (add_state (fill_Table_ds cs) (canon (derivative c e))) e c
                                    (canon (derivative c e))) (canon (derivative c e)) orig
                         (Pos.pred_double p0) (acc_rec_call_xO p0~0 p0 Ha eq_refl)
                     end
                   end)
              /\ (fix fill_Table_ds (bs' : list Sigma) : Table :=
                   match bs' with
                   | [] => T
                   | c :: cs =>
                     match get_eq (fill_Table_ds cs) (canon (derivative c e)) with
                     | Some e' => set_Table (fill_Table_ds cs) e c e'
                     | None =>
                       fill_Table_all'
                         (set_Table (add_state (fill_Table_ds cs) (canon (derivative c e))) e c
                                    (canon (derivative c e))) (canon (derivative c e)) bs n
                     end
                   end)
                = (fix fill_Table_ds (bs' : list Sigma) : Table :=
                     match bs' with
                     | [] => T
                     | c :: cs =>
                       match get_eq (fill_Table_ds cs) (canon (derivative c e)) with
                       | Some e' => set_Table (fill_Table_ds cs) e c e'
                       | None =>
                         fill_Table_all'
                           (set_Table (add_state (fill_Table_ds cs) (canon (derivative c e))) e c
                                      (canon (derivative c e))) (canon (derivative c e)) orig n
                       end
                     end)).
        { eauto. }
        destruct H1 as (orig & H1 & H2).
        rewrite H1. rewrite H2. clear H1 H2.
        induction bs; auto.
        rewrite IHbs. dm.
        clear IHbs E0. rewrite H0 with (y := (Pos.pred_double p0)); auto. clear H0.
          2: {
            unfold ltof.
            assert(Pos.pred_double p0 = Pos.pred (xO p0)).
            { auto. }
            rewrite H1. rewrite Nat.succ_lt_mono. repeat rewrite <- Pos2Nat.inj_succ.
            rewrite Pos.succ_pred; auto. intros; discriminate.
          }
          assert(n = (Init.Nat.pred (Pos.to_nat (Pos.pred_double p0)))).
          {
            rewrite <- Pos2Nat.inj_pred in E1.
            2: { constructor. }
            simpl in E1. rewrite E1. lia.
          }
          rewrite H0. auto.
      - simpl. rewrite filler_eq_body. auto.
    Qed.

    (** [fill_Table_all'_bin] with any [Acc] witness equals [fill_Table_all'] at the corresponding nat fuel; convenience wrapper. *)
    Theorem fill_bin'_equiv : forall (p : positive) (Ha : Acc (ltof positive (Pos.to_nat)) p)
                                 (bs : list Sigma) (T : Table) (e : regex),
        fill_Table_all'_bin T e bs p Ha = fill_Table_all' T e bs (pred (Pos.to_nat p)).
    Proof.
      intros. eapply fill_bin'_equiv'; eauto.
    Qed.

    (** [fill_Table_all_bin] equals [fill_Table_all] at the corresponding nat fuel. *)
    Theorem fill_bin_equiv : forall (p : positive) (bs : list Sigma) (T : Table) (e : regex),
        fill_Table_all_bin T e bs p = fill_Table_all T e bs (pred (Pos.to_nat p)).
    Proof.
      intros. unfold fill_Table_all. unfold fill_Table_all_bin. apply fill_bin'_equiv.
    Qed.


    (** [fill_Table_all_bin] preserves [derived]; proved by reduction to [derived_closure_all] via [fill_bin_equiv]. *)
    Theorem derived_closure_all_bin : forall p bs e T T',
        derived T
        -> T' = fill_Table_all_bin T e bs p
        -> derived T'.
    Proof.
      intros. rewrite fill_bin_equiv in H0. eapply derived_closure_all; eauto.
    Qed.

  End binary.

  (** * Closure of the filled state set

      [fill_Table_all'] explores the Brzozowski state graph depth-first,
      spending one unit of fuel per level of the DFS.  A level is only
      entered right after a state that was genuinely absent from the table
      has been added, so the depth of the DFS is bounded by the number of
      distinct states it can ever reach.  Consequently, if we are handed a
      finite universe [U] that contains the start state and is closed under
      [canon]-of-derivative, then fuel exceeding [length U] guarantees that
      the fill runs to completion: the resulting state set is itself closed
      under [canon]-of-derivative, and every table entry is literally the
      canonical derivative it stands for.

      Those two facts are exactly the certificate the interned DFA needs
      ([IntDFA.closed_check]).  [CanonNF] supplies the universe. *)
  Module Export FillClosure.

    (** The state set of [T] lies inside the universe [U]. *)
    Definition StatesIn (U : list regex) (T : Table) : Prop :=
      forall s, reFS.In s (get_states T) -> List.In s U.

    (** [T'] retains every state of [T]. *)
    Definition Grew (T T' : Table) : Prop :=
      forall s, reFS.In s (get_states T) -> reFS.In s (get_states T').

    (** Every [bs]-successor of [e] is already a state of [T]. *)
    Definition Covers (bs : list Sigma) (T : Table) (e : regex) : Prop :=
      forall c, List.In c bs -> reFS.In (canon (derivative c e)) (get_states T).

    (** [T]'s state set is closed under [bs]-successors, except possibly at
        the states listed in [Rs] -- the roots the fill is still working on. *)
    Definition ClosedExc (bs : list Sigma) (T : Table) (Rs : list regex) : Prop :=
      forall s, reFS.In s (get_states T) ->
                List.In s Rs \/ Covers bs T s.

    (** Full closure: the [Rs]-free case. *)
    Definition StatesClosed (bs : list Sigma) (T : Table) : Prop :=
      forall s, reFS.In s (get_states T) -> Covers bs T s.

    (** [U] is closed under [bs]-successors. *)
    Definition UClosed (U : list regex) (bs : list Sigma) : Prop :=
      forall x c, List.In x U -> List.In c bs ->
                  List.In (canon (derivative c x)) U.

    (** Every table entry is literally the canonical derivative of its key. *)
    Definition DerivedEq (T : Table) : Prop :=
      forall s c s', get_Table T s c = Some s' -> s' = canon (derivative c s).

    (** [NoDupA] at the set's equality is ordinary [NoDup] once membership is
        reflected through [InA]. *)
    Lemma NoDupA_NoDup : forall l : list regex,
        NoDupA reFS.E.eq l -> NoDup l.
    Proof.
      induction l as [| h t IH]; intros H; inversion H; subst; constructor.
      - intros C. apply H2. apply InA_alt. exists h. split; auto.
        apply reFS.E.eq_refl.
      - auto.
    Qed.

    (** A state set confined to [U] cannot outgrow [U]. *)
    Lemma card_le : forall U T,
        StatesIn U T -> reFS.cardinal (get_states T) <= length U.
    Proof.
      intros U T H. rewrite reFS.cardinal_1. apply NoDup_incl_length.
      - apply NoDupA_NoDup. apply reFS.elements_3w.
      - intros x Hx. apply H. apply reFS.elements_2. apply InA_alt.
        exists x. split; [apply reFS.E.eq_refl | auto].
    Qed.

    (** [set_Table] leaves the state set alone, so it preserves membership. *)
    Lemma set_Table_In : forall T e a r s,
        reFS.In s (get_states (set_Table T e a r))
        <-> reFS.In s (get_states T).
    Proof. intros. rewrite set_Table_states. reflexivity. Qed.

    (** [DerivedEq] survives an entry that records a canonical derivative. *)
    Lemma DerivedEq_set : forall T e a,
        DerivedEq T -> DerivedEq (set_Table T e a (canon (derivative a e))).
    Proof.
      intros T e a HD s c s' H.
      destruct (Sigma_dec c a) as [Hc | Hc]; destruct (regex_dec s e) as [Hs | Hs].
      - subst. rewrite correct_Table in H. inv H. auto.
      - rewrite moot_setTable in H by auto. apply HD. auto.
      - rewrite moot_setTable in H by auto. apply HD. auto.
      - rewrite moot_setTable in H by auto. apply HD. auto.
    Qed.

    (** [add_state] does not touch the transition map. *)
    Lemma DerivedEq_add : forall T r, DerivedEq T -> DerivedEq (add_state T r).
    Proof.
      intros T r HD s c s' H. rewrite <- moot_add_state in H. apply HD. auto.
    Qed.

    (** The heart of the argument: with fuel beyond the size of the universe,
        one [fill_Table_all'] call closes off its root [e] and everything it
        discovers, leaving only the outer roots [Rs] outstanding. *)
    Lemma fill_closure' : forall n U bs T e Rs,
        UClosed U bs ->
        List.In e U ->
        StatesIn U T ->
        DerivedEq T ->
        ClosedExc bs T (e :: Rs) ->
        length U < reFS.cardinal (get_states T) + n ->
        StatesIn U (fill_Table_all' T e bs n)
        /\ Grew T (fill_Table_all' T e bs n)
        /\ reFS.cardinal (get_states T)
           <= reFS.cardinal (get_states (fill_Table_all' T e bs n))
        /\ DerivedEq (fill_Table_all' T e bs n)
        /\ ClosedExc bs (fill_Table_all' T e bs n) Rs
        /\ Covers bs (fill_Table_all' T e bs n) e.
    Proof.
      intros n. induction n as [| m IHm];
        intros U bs T e Rs HU He HS HD HC Hf.
      { exfalso. pose proof (card_le U T HS). simpl in Hf. lia. }
      simpl.
      match goal with
      | |- StatesIn U (?f bs) /\ _ => set (F := f)
      end.
      assert (Fnil : F [] = T) by reflexivity.
      assert (Fcons : forall c cs,
                 F (c :: cs)
                 = let T1 := F cs in
                   let d := canon (derivative c e) in
                   match get_eq T1 d with
                   | None => fill_Table_all'
                               (set_Table (add_state T1 d) e c d) d bs m
                   | Some e' => set_Table T1 e c e'
                   end) by reflexivity.
      clearbody F.
      (* The inner recursion over the alphabet, one character at a time. *)
      assert (MAIN : forall bs', incl bs' bs ->
                 StatesIn U (F bs')
                 /\ Grew T (F bs')
                 /\ reFS.cardinal (get_states T)
                    <= reFS.cardinal (get_states (F bs'))
                 /\ DerivedEq (F bs')
                 /\ ClosedExc bs (F bs') (e :: Rs)
                 /\ (forall c, List.In c bs' ->
                               reFS.In (canon (derivative c e)) (get_states (F bs')))).
      { induction bs' as [| c cs IHcs]; intros Hincl.
        - rewrite Fnil. repeat split; auto.
          + intros s Hs. auto.
          + intros c Hc. inv Hc.
        - assert (Hc : List.In c bs) by (apply Hincl; left; auto).
          assert (Hcs : incl cs bs) by (intros x Hx; apply Hincl; right; auto).
          destruct (IHcs Hcs) as (HS1 & HG1 & HK1 & HD1 & HC1 & HV1).
          rewrite Fcons. cbv zeta.
          remember (F cs) as T1 eqn:HT1.
          remember (canon (derivative c e)) as d eqn:Hd.
          assert (HdU : List.In d U) by (subst d; apply HU; auto).
          destruct (get_eq T1 d) as [r |] eqn:E.
          + (* the successor is already a state: only a table entry is added *)
            apply get_eq_correct in E. destruct E as [Er Eeq].
            apply regex_eq_correct in Eeq. subst r.
            assert (Hst : forall s, reFS.In s (get_states (set_Table T1 e c d))
                                    <-> reFS.In s (get_states T1))
              by (intros; apply set_Table_In).
            assert (Hste : get_states (set_Table T1 e c d) = get_states T1)
              by apply set_Table_states.
            repeat split.
            * intros s Hs. apply HS1. apply Hst. auto.
            * intros s Hs. apply Hst. apply HG1. auto.
            * rewrite Hste. auto.
            * subst d. apply DerivedEq_set. auto.
            * intros s Hs. rewrite Hste in Hs.
              destruct (HC1 s Hs) as [Hin | Hcov]; [left; auto | right].
              intros c' Hc'. rewrite Hste. apply Hcov. auto.
            * intros c' Hc'. rewrite Hste. destruct Hc' as [<- | Hc'].
              -- subst d. auto.
              -- apply HV1. auto.
          + (* a genuinely new state: add it, then recurse into it *)
            apply get_eq_None in E.
            remember (add_state T1 d) as T2 eqn:HT2.
            remember (set_Table T2 e c d) as T3 eqn:HT3.
            assert (Hst3 : get_states T3 = get_states T2)
              by (subst T3; apply set_Table_states).
            assert (HdIn : reFS.In d (get_states T3))
              by (rewrite Hst3; subst T2; apply correct_states).
            assert (Hmono : forall s, reFS.In s (get_states T1) ->
                                      reFS.In s (get_states T3)).
            { intros s Hs. rewrite Hst3. subst T2. apply add_state_mono. auto. }
            assert (HS3 : StatesIn U T3).
            { intros s Hs. rewrite Hst3 in Hs. subst T2.
              apply add_state_states in Hs. destruct Hs as [-> | Hs]; auto. }
            assert (HD3 : DerivedEq T3).
            { subst T3. rewrite Hd. apply DerivedEq_set. subst T2.
              apply DerivedEq_add. auto. }
            assert (HK3 : reFS.cardinal (get_states T3)
                          = S (reFS.cardinal (get_states T1)))
              by (rewrite Hst3; subst T2; apply add_state_cardinal; auto).
            assert (HC3 : ClosedExc bs T3 (d :: e :: Rs)).
            { intros s Hs. rewrite Hst3 in Hs. subst T2.
              apply add_state_states in Hs. destruct Hs as [-> | Hs];
                [left; left; auto |].
              destruct (HC1 s Hs) as [Hin | Hcov].
              - left. right. auto.
              - right. intros c' Hc'. apply Hmono. apply Hcov. auto. }
            assert (Hf3 : length U < reFS.cardinal (get_states T3) + m) by lia.
            destruct (IHm U bs T3 d (e :: Rs) HU HdU HS3 HD3 HC3 Hf3)
              as (HS4 & HG4 & HK4 & HD4 & HC4 & HV4).
            repeat split; auto.
            * intros s Hs. apply HG4. apply Hmono. apply HG1. auto.
            * lia.
            * intros c' Hc'. destruct Hc' as [<- | Hc'].
              -- apply HG4. rewrite <- Hd. auto.
              -- apply HG4. apply Hmono. apply HV1. auto. }
      destruct (MAIN bs (incl_refl bs)) as (HSf & HGf & HKf & HDf & HCf & HVf).
      repeat split; auto.
      intros s Hs. destruct (HCf s Hs) as [Hin | Hcov]; [| right; auto].
      destruct Hin as [<- | Hin]; [right; exact HVf | left; auto].
    Qed.

    (** The top-level statement about [fill_Table_all]: a universe closed
        under [canon]-of-derivative and larger than the fuel is all it takes
        for the resulting table to be closed and faithfully derived. *)
    Theorem fill_Table_all_closed : forall U bs e n,
        UClosed U bs ->
        List.In (canon e) U ->
        length U < n ->
        DerivedEq (fill_Table_all emptyTable e bs n)
        /\ StatesClosed bs (fill_Table_all emptyTable e bs n)
        /\ Covers bs (fill_Table_all emptyTable e bs n) (canon e).
    Proof.
      intros U bs e n HU He Hn. unfold fill_Table_all.
      assert (HS : StatesIn U emptyTable).
      { intros s Hs. rewrite empty_states in Hs.
        exfalso. eapply reFS.empty_1. exact Hs. }
      assert (HD : DerivedEq emptyTable).
      { intros s c s' H. rewrite correct_emptyTable in H. discriminate. }
      assert (HC : ClosedExc bs emptyTable (canon e :: [])).
      { intros s Hs. rewrite empty_states in Hs.
        exfalso. eapply reFS.empty_1. exact Hs. }
      assert (Hf : length U < reFS.cardinal (get_states emptyTable) + n) by lia.
      destruct (fill_closure' n U bs emptyTable (canon e) [] HU He HS HD HC Hf)
        as (_ & _ & _ & HD' & HC' & HV').
      repeat split; auto.
      intros s Hs. destruct (HC' s Hs) as [[] | Hcov]. auto.
    Qed.

    (** The two invariants that hold with *no* condition on the fuel: the
        fill never leaves the universe, and every entry it writes is the
        canonical derivative of its key.  These are what the interned
        builder's saturation pass runs on -- unlike [fill_closure'] they do
        not need a fuel bound, which matters because [length (Superset e)] is
        astronomically large and so cannot be materialised as fuel. *)
    Lemma fill_invariants : forall n U bs T e,
        UClosed U bs ->
        List.In e U ->
        StatesIn U T ->
        DerivedEq T ->
        StatesIn U (fill_Table_all' T e bs n)
        /\ DerivedEq (fill_Table_all' T e bs n)
        /\ Grew T (fill_Table_all' T e bs n).
    Proof.
      intros n. induction n as [| m IHm]; intros U bs T e HU He HS HD.
      { simpl. repeat split; auto. intros s Hs; auto. }
      simpl.
      match goal with
      | |- StatesIn U (?f bs) /\ _ => set (F := f)
      end.
      assert (Fnil : F [] = T) by reflexivity.
      assert (Fcons : forall c cs,
                 F (c :: cs)
                 = let T1 := F cs in
                   let d := canon (derivative c e) in
                   match get_eq T1 d with
                   | None => fill_Table_all'
                               (set_Table (add_state T1 d) e c d) d bs m
                   | Some e' => set_Table T1 e c e'
                   end) by reflexivity.
      clearbody F.
      assert (MAIN : forall bs', incl bs' bs ->
                 StatesIn U (F bs') /\ DerivedEq (F bs') /\ Grew T (F bs')).
      { induction bs' as [| c cs IHcs]; intros Hincl.
        - rewrite Fnil. repeat split; auto. intros s Hs; auto.
        - assert (Hc : List.In c bs) by (apply Hincl; left; auto).
          assert (Hcs : incl cs bs) by (intros x Hx; apply Hincl; right; auto).
          destruct (IHcs Hcs) as (HS1 & HD1 & HG1).
          rewrite Fcons. cbv zeta.
          remember (F cs) as T1 eqn:HT1.
          remember (canon (derivative c e)) as d eqn:Hd.
          assert (HdU : List.In d U) by (subst d; apply HU; auto).
          destruct (get_eq T1 d) as [r |] eqn:E.
          + apply get_eq_correct in E. destruct E as [Er Eeq].
            apply regex_eq_correct in Eeq. subst r.
            assert (Hste : get_states (set_Table T1 e c d) = get_states T1)
              by apply set_Table_states.
            repeat split.
            * intros s Hs. rewrite Hste in Hs. auto.
            * subst d. apply DerivedEq_set. auto.
            * intros s Hs. rewrite Hste. auto.
          + remember (add_state T1 d) as T2 eqn:HT2.
            remember (set_Table T2 e c d) as T3 eqn:HT3.
            assert (Hst3 : get_states T3 = get_states T2)
              by (subst T3; apply set_Table_states).
            assert (Hmono : forall s, reFS.In s (get_states T1) ->
                                      reFS.In s (get_states T3)).
            { intros s Hs. rewrite Hst3. subst T2. apply add_state_mono. auto. }
            assert (HS3 : StatesIn U T3).
            { intros s Hs. rewrite Hst3 in Hs. subst T2.
              apply add_state_states in Hs. destruct Hs as [-> | Hs]; auto. }
            assert (HD3 : DerivedEq T3).
            { subst T3. rewrite Hd. apply DerivedEq_set. subst T2.
              apply DerivedEq_add. auto. }
            destruct (IHm U bs T3 d HU HdU HS3 HD3) as (HS4 & HD4 & HG4).
            repeat split; auto.
            intros s Hs. apply HG4, Hmono, HG1, Hs. }
      apply (MAIN bs (incl_refl bs)).
    Qed.

    (** [fill_Table_all] from the empty table, unconditionally. *)
    Theorem fill_Table_all_invariants : forall U bs e n,
        UClosed U bs ->
        List.In (canon e) U ->
        StatesIn U (fill_Table_all emptyTable e bs n)
        /\ DerivedEq (fill_Table_all emptyTable e bs n).
    Proof.
      intros U bs e n HU He. unfold fill_Table_all.
      assert (HS : StatesIn U emptyTable).
      { intros s Hs. rewrite empty_states in Hs.
        exfalso. eapply reFS.empty_1. exact Hs. }
      assert (HD : DerivedEq emptyTable).
      { intros s c s' H. rewrite correct_emptyTable in H. discriminate. }
      destruct (fill_invariants n U bs emptyTable (canon e) HU He HS HD)
        as (H1 & H2 & _). auto.
    Qed.

    Theorem fill_Table_all_bin_invariants : forall U bs e p,
        UClosed U bs ->
        List.In (canon e) U ->
        StatesIn U (fill_Table_all_bin emptyTable e bs p)
        /\ DerivedEq (fill_Table_all_bin emptyTable e bs p).
    Proof.
      intros. rewrite fill_bin_equiv.
      apply fill_Table_all_invariants with (U := U); auto.
    Qed.

    (** Same, for the binary-fuel filler actually used by [regex2dfa]. *)
    Theorem fill_Table_all_bin_closed : forall U bs e p,
        UClosed U bs ->
        List.In (canon e) U ->
        length U < pred (Pos.to_nat p) ->
        DerivedEq (fill_Table_all_bin emptyTable e bs p)
        /\ StatesClosed bs (fill_Table_all_bin emptyTable e bs p)
        /\ Covers bs (fill_Table_all_bin emptyTable e bs p) (canon e).
    Proof.
      intros. rewrite fill_bin_equiv. apply fill_Table_all_closed with (U := U); auto.
    Qed.

  End FillClosure.

End DefsFn.

(** Module type that packages [DefsFn] as a named signature. *)
Module Type DefsT (R : Regex.T) (TabTy : Table R).
  Include DefsFn R TabTy.
End DefsT.

(** Bundle module type combining a regex alphabet, a Table implementation, and the Defs functor. *)
Module Type T.
  Declare Module R : Regex.T.
  Declare Module TabTy : Table R.
  Declare Module Defs : DefsT R TabTy.
  Export R.
  Export R.Ty.
  Export R.Defs.
  Export TabTy.
  Export Defs.
End T.
