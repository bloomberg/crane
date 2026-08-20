(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List OrderedType OrderedTypeAlt OrderedTypeEx.
From Crane.Libraries.ParseALot.Parser Require Import Tactics.
Import ListNotations.

(** Auxiliary lemmas about a [UsualOrderedType] used throughout the ordering modules. *)
Module UOTFacts (U : UsualOrderedType).

  (** Strict order is irreflexive: no element is less than itself. *)
  Lemma lt_refl_contra :
    forall x,
      ~ U.lt x x.
  Proof.
    intros x hl; eapply U.lt_not_eq; eauto; red; auto.
  Qed.
  
  (** If [x < y] then [compare x y] returns [LT], witnessed by the proof of [lt x y]. *)
  Lemma lt_compare_LT :
    forall x y,
      U.lt x y
      -> exists hl, U.compare x y = LT hl.
  Proof.
    intros x y hl.
    destruct (U.compare x y) as [hl' | he | hl']; eauto.
    - exfalso.
      red in he; subst.
      eapply lt_refl_contra; eauto.
    - exfalso.
      eapply U.lt_trans in hl'; eauto.
      eapply lt_refl_contra; eauto.
  Qed.

  (** [compare x y] returns [EQ] if and only if [x = y]. *)
  Lemma eq_compare_EQ :
    forall x y,
      (exists heq, U.compare x y = EQ heq) <-> x = y.
  Proof.
    unfold U.eq; intros x y; split; [intros hex | intros heq]; subst.
    - destruct hex; auto.
    - destruct (U.compare y y).
      + exfalso; eapply lt_refl_contra; eauto. 
      + red in e; subst; eauto.
      + exfalso; eapply lt_refl_contra; eauto.
  Qed.

  (** Every element compares equal to itself. *)
  Lemma compare_refl :
    forall x,
      (exists heq,
          U.compare x x = EQ heq).
  Proof.
    intros x; apply eq_compare_EQ; auto. 
  Qed.

End UOTFacts.

(** Interface for types equipped with a decidable three-way comparison satisfying reflexivity and transitivity. *)
Module Type UsualComparableType.

  Parameter t : Type.

  Parameter compare : t -> t -> comparison.

  Parameter compare_eq :
    forall x y : t,
      compare x y = Eq <-> x = y. 

  Parameter compare_trans :
    forall (c : comparison) (x y z : t),
      compare    x y = c
      -> compare y z = c
      -> compare x z = c.

End UsualComparableType.

(** Functor lifting a [UsualComparableType] into a full [UsualOrderedType] by defining [lt] via [C.compare]. *)
Module UOTFromUCT (C : UsualComparableType) <: UsualOrderedType.

  (** The carrier type, inherited from [C]. *)
  Definition t := C.t.

  (** Equality and its reflexivity, symmetry, and transitivity witnesses, using Leibniz equality. *)
  Definition eq       := @eq t.
  Definition eq_refl  := @eq_refl t.
  Definition eq_sym   := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  (** Strict order: [x < y] iff [C.compare x y = Lt]. *)
  Definition lt (x y : t) : Prop :=
    match C.compare x y with
    | Lt => True
    | _  => False
    end.

  (** Transitivity of [lt] follows from transitivity of [C.compare]. *)
  Lemma lt_trans :
    forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt; intros x y z hlt hlt'.
    destruct (C.compare x y) eqn:hc  ;
      destruct (C.compare y z) eqn:hc' ;
      destruct (C.compare x z) eqn:hc''; auto.
    - eapply C.compare_trans in hc'; eauto; tc.
    - eapply C.compare_trans in hc'; eauto; tc.
  Qed.
  
  (** A strictly smaller element cannot equal the larger one, by [C.compare_eq]. *)
  Lemma lt_not_eq :
    forall x y, lt x y -> ~ x = y.
  Proof.
    unfold lt; intros x y hl heq.
    apply C.compare_eq in heq.
    rewrite heq in hl; inv hl.
  Qed.

  (** [C.compare x x = Eq] holds because equality is reflexive. *)
  Lemma compare_refl :
    forall x, C.compare x x = Eq.
  Proof.
    intros x; apply C.compare_eq; auto.
  Qed.
  
  (** [C.compare x y] is the opposite of [C.compare y x], establishing anti-symmetry. *)
  Lemma compare_sym :
    forall x y, C.compare x y = CompOpp (C.compare y x).
  Proof.
    intros x y; destruct (C.compare x y) eqn:hc.
    - apply C.compare_eq in hc; subst.
      rewrite compare_refl; auto.
    - destruct (C.compare y x) eqn:hc'; auto.
      + exfalso; apply C.compare_eq in hc'; subst.
        rewrite compare_refl in hc; tc.
      + exfalso; eapply C.compare_trans in hc'; eauto.
        rewrite compare_refl in hc'; tc.
    - destruct (C.compare y x) eqn:hc'; auto.
      + exfalso; apply C.compare_eq in hc'; subst.
        rewrite compare_refl in hc; tc.
      + exfalso; eapply C.compare_trans in hc'; eauto.
        rewrite compare_refl in hc'; tc.
  Qed.

  (** Three-way comparison returning a [Compare lt eq] proof term, dispatching on [C.compare]. *)
  Definition compare :
    forall x y,
      Compare lt eq x y.
  Proof.
    intros x y; destruct (C.compare x y) eqn:hc.
    - apply EQ; apply C.compare_eq; auto.
    - apply LT; unfold lt; rewrite hc; auto.
    - apply GT; unfold lt; rewrite compare_sym in hc.
      destruct (C.compare y x) eqn:hc'; sis; tc; auto.
  Defined.

  (** Decidable equality, obtained by checking whether [C.compare] returns [Eq]. *)
  Definition eq_dec :
    forall x y : t,
      {x = y} + {x <> y}.
  Proof.
    intros x y; destruct (C.compare x y) eqn:hc.
    - left; apply C.compare_eq; auto.
    - right; intros heq; apply C.compare_eq in heq; tc.
    - right; intros heq; apply C.compare_eq in heq; tc.
  Defined.

End UOTFromUCT.

(** Lifts a [UsualOrderedType] on [E.t] to one on [option E.t], ordering [None] below every [Some]. *)
Module OptionAsUOT (E : UsualOrderedType) <: UsualOrderedType.

  Module F := UOTFacts E.

  (** The carrier type [option E.t]. *)
  Definition t := option E.t.

  (** Leibniz equality witnesses for [option E.t]. *)
  Definition eq       := @eq t.
  Definition eq_refl  := @eq_refl t.
  Definition eq_sym   := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  (** Strict order: [None < Some _] and [Some x < Some y] iff [E.lt x y]. *)
  Definition lt o o' :=
    match o, o' with
    | None, None     => False
    | None, Some _   => True
    | Some _, None   => False
    | Some x, Some y => E.lt x y
    end.

  (** Transitivity: the only nontrivial case is [Some x < Some y < Some z], reducing to [E.lt_trans]. *)
  Lemma lt_trans :
    forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt; intros x y z hl hl';
      destruct x as [x |]; destruct y as [y |]; destruct z as [z |];
        try contradiction; auto.
    eapply E.lt_trans; eauto.
  Qed.

  (** A strictly smaller option value cannot be equal to the larger one. *)
  Lemma lt_not_eq :
    forall x y,
      lt x y -> ~ x = y.
  Proof.
    intros x y hl heq; destruct x as [x |]; destruct y as [y |]; tc; auto.
    inv heq; eapply F.lt_refl_contra; eauto.
  Qed.

  (** Three-way comparison for option values, delegating to [E.compare] in the [Some/Some] case. *)
  Definition compare (x y : t) : Compare lt eq x y.
    refine (match x as x' return x = x' -> _ with
            | None =>
              fun heq =>
                match y as y' return y = y' -> _ with
                | None    => fun heq' => EQ _
                | Some e' => fun heq' => LT _
                end (eq_refl y)
            | Some e =>
              fun heq =>
                match y as y' return y = y' -> _ with
                | None    => fun heq' => GT _
                | Some e' => fun heq' =>
                               match E.compare e e' with
                               | LT hl => LT _
                               | GT hl => GT _
                               | EQ he => EQ _
                               end
                end (eq_refl y)
            end (eq_refl x));
      red; unfold E.eq in *; subst; auto.
  Defined.
  
  (** Decidable equality for option values, delegating to [E.eq_dec] in the [Some/Some] case. *)
  Definition eq_dec (x y : t) : {x = y} + {x <> y}.
    refine (match x as x' return x = x' -> _ with
            | None =>
              fun heq =>
                match y as y' return y = y' -> _ with
                | None    => fun heq' => left _
                | Some e' => fun heq' => right _
                end (eq_refl y)
            | Some e =>
              fun heq =>
                match y as y' return y = y' -> _ with
                | None    => fun heq' => right _
                | Some e' => fun heq' =>
                               match E.eq_dec e e' with
                               | left he => left _
                               | right hn => right _
                               end
                end (eq_refl y)
            end (eq_refl x));
      unfold not, E.eq in *; subst; tc.
  Defined.

End OptionAsUOT.

(** Lifts a [UsualOrderedType] on [E.t] to one on [list E.t] using lexicographic order (shorter lists come first). *)
Module ListAsUOT (E : UsualOrderedType) <: UsualOrderedType.

  Module F := UOTFacts E.

  (** The carrier type [list E.t]. *)
  Definition t := list E.t.

  (** Leibniz equality witnesses for [list E.t]. *)
  Definition eq       := @eq t.
  Definition eq_refl  := @eq_refl t.
  Definition eq_sym   := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  (** Lexicographic strict order on lists: [] < any non-empty list, and cons cells are compared head-first then tail-recursively. *)
  Fixpoint lt xs ys :=
    match xs, ys with
    | [], []             => False
    | [], _ :: _         => True
    | _ :: _, []         => False
    | x :: xs', y :: ys' =>
      match E.compare x y with
      | LT _ => True
      | EQ _ => lt xs' ys'
      | GT _ => False
      end
    end.

  (** When [x::xs < y::ys] and [y::ys < x::zs], the heads must be equal. *)
  Lemma lt_trans_heads_eq :
    forall x y xs ys zs,
      lt (x :: xs) (y :: ys)
      -> lt (y :: ys) (x :: zs)
      -> y = x.
  Proof.
    intros x y xs ys zs hl hl'; red in hl, hl'.
    destruct (E.compare x y) as [hel | hee | hel];
      destruct (E.compare y x) as [hel' | hee' | hel'];
      try contradiction; auto.
    eapply E.lt_trans in hel'; eauto.
    exfalso; eapply F.lt_refl_contra; eauto.
  Qed.

  (** Lexicographic order on cons-lists with equal heads reduces to order on the tails. *)
  Lemma lt_inv_cons :
    forall x xs ys,
      lt (x :: xs) (x :: ys)
      -> lt xs ys.
  Proof.
    intros x xs ys hl; red in hl.
    destruct (E.compare x x); try contradiction; auto.
    exfalso; eapply F.lt_refl_contra; eauto. 
  Qed.

  (** When [x::xs < y::ys < z::zs], the first component satisfies [E.lt x z] or [z = x]. *)
  Lemma lt_trans_heads_lt_or_eq :
    forall x y z xs ys zs,
      lt (x :: xs) (y :: ys)
      -> lt (y :: ys) (z :: zs)
      -> E.lt x z \/ z = x.
  Proof.
    intros x y z xs ys zs hl hl'; red in hl, hl'.
    destruct (E.compare x y) as [hel | hee | hel];
      destruct (E.compare y z) as [hel' | hee' | hel'];
      try contradiction; auto.
    - left; eapply E.lt_trans; eauto.
    - left; red in hee'; subst; auto.
    - left; red in hee ; subst; auto.
    - right; red in hee; red in hee'; subst; auto.
  Qed.
  
  (** Lexicographic order on lists is transitive, proved by induction on [xs]. *)
  Lemma lt_trans :
    forall xs ys zs,
      lt xs ys -> lt ys zs -> lt xs zs.
  Proof.
    intros xs; induction xs as [| x xs IH];
      intros ys zs hl hl'; destruct ys as [| y ys]; destruct zs as [| z zs]; try contradiction; auto.
    red; destruct (E.compare x z) as [hel | hee | hel]; auto.
    - fold lt; red in hee; subst.
      assert (heq : y = z) by (eapply lt_trans_heads_eq; eauto); subst.
      apply lt_inv_cons in hl; apply lt_inv_cons in hl'; eauto.
    - eapply lt_trans_heads_lt_or_eq in hl'; eauto.
      destruct hl' as [hl' | ?]; subst.
      + eapply E.lt_trans in hl'; eauto.
        eapply E.lt_not_eq; eauto; red; auto.
      + eapply E.lt_not_eq; eauto; red; auto.
  Qed.
  
  (** A lexicographically smaller list cannot equal the larger one. *)
  Lemma lt_not_eq :
    forall xs ys,
      lt xs ys -> ~ xs = ys.
  Proof.
    intros xs; induction xs as [| x xs IH];
      intros ys hl heq; destruct ys as [| y ys]; tc; inv heq; auto.
    red in hl; destruct (E.compare y y); tc.
    - eapply E.lt_not_eq; eauto; red; auto.
    - eapply IH; eauto. 
  Qed.

  (** Three-way lexicographic comparison on lists, computed recursively alongside [lt]. *)
  Fixpoint compare (xs ys : list E.t) : Compare lt eq xs ys.
    refine (match xs as xs' return xs = xs' -> _ with
            | [] =>
              fun heq =>
                match ys as ys' return ys = ys' -> _ with
                | []     => fun heq' => EQ _
                | _ :: _ => fun heq' => LT _
                end (eq_refl ys)
            | x :: xs' =>
              fun heq =>
                match ys as ys' return ys = ys' -> _ with
                | []       => fun heq' => GT _
                | y :: ys' => fun heq' =>
                                match E.compare x y with
                                | LT hl => LT _
                                | GT hl => GT _
                                | EQ he =>
                                  match compare xs' ys' with
                                  | LT hl  => LT _
                                  | GT hl  => GT _
                                  | EQ he' => EQ _
                                  end
                                end
                end (eq_refl ys)
            end (eq_refl xs));
      unfold eq, E.eq in *; try red; subst; auto.
    - apply F.lt_compare_LT in hl.
      destruct hl as [hl hc]; rewrite hc; auto.
    - pose proof (F.compare_refl y) as heq.
      destruct heq as [heq hc]; rewrite hc; auto.
    - pose proof (F.compare_refl y) as heq.
      destruct heq as [heq hc]; rewrite hc; auto.
    - apply F.lt_compare_LT in hl.
      destruct hl as [hl hc]; rewrite hc; auto.
  Defined.

  (** Decidable equality on lists, recursing on heads via [E.eq_dec]. *)
  Fixpoint eq_dec (xs ys : t) : {xs = ys} + {xs <> ys}.
    refine (match xs as xs' return xs = xs' -> _ with
            | [] =>
              fun heq =>
                match ys as ys' return ys = ys' -> _ with
                | []     => fun heq' => left _
                | _ :: _ => fun heq' => right _
                end (eq_refl ys)
            | x :: xs' =>
              fun heq =>
                match ys as ys' return ys = ys' -> _ with
                | []       => fun heq' => right _
                | y :: ys' => fun heq' =>
                                match E.eq_dec x y with
                                | left _ =>
                                  match eq_dec xs' ys' with
                                  | left _  => left _
                                  | right _ => right _
                                  end
                                | right _ => right _
                                end
                end (eq_refl ys)
            end (eq_refl xs)); tc.
  Defined.

End ListAsUOT.

(** Lifts two [UsualOrderedType]s to one on their cartesian product using lexicographic order (first by [A], then by [B]). *)
Module PairAsUOT (A : UsualOrderedType) (B : UsualOrderedType) <: UsualOrderedType.

  Module FA := UOTFacts A.
  Module FB := UOTFacts B.

  (** The carrier type [A.t * B.t]. *)
  Definition t := (A.t * B.t)%type.

  (** Leibniz equality witnesses for the pair type. *)
  Definition eq       := @eq t.
  Definition eq_refl  := @eq_refl t.
  Definition eq_sym   := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  (** Lexicographic strict order on pairs: compare first components, break ties with second components. *)
  Definition lt x y :=
    match x, y with
    | (a, b), (a', b') =>
      match A.compare a a' with
      | LT _ => True
      | GT _ => False
      | EQ _ =>
        match B.compare b b' with
        | LT _ => True
        | _    => False
        end
      end
    end.

  (** Transitivity of the pair order, combining transitivity of [A.lt] and [B.lt]. *)
  Lemma lt_trans :
    forall x y z,
      lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt; intros (a, b) (a', b') (a'', b'') hl hl'.
    destruct (A.compare a a') as [ha | ha | ha]; try contradiction.
    - destruct (A.compare a' a'') as [ha' | ha' | ha']; try contradiction.
      + eapply A.lt_trans in ha'; eauto.
        apply FA.lt_compare_LT in ha'.
        destruct ha' as (hl'' & heq); rewrite heq; auto.
      + red in ha'; subst.
        apply FA.lt_compare_LT in ha.
        destruct ha as (hl'' & heq); rewrite heq; auto.
    - red in ha; subst.
      destruct (A.compare a' a'') as [ha' | ha' | ha']; try contradiction; auto.
      destruct (B.compare b b') as [hb | hb | hb]; try contradiction.
      destruct (B.compare b' b'') as [hb' | hb' | hb']; try contradiction.
      eapply B.lt_trans in hb'; eauto.
      apply FB.lt_compare_LT in hb'.
      destruct hb' as (hl'' & heq); rewrite heq; auto.
  Qed.

  (** A strictly smaller pair cannot equal the larger one: reflexivity of both components would contradict [lt]. *)
  Lemma lt_not_eq :
    forall x y,
      lt x y -> ~ x = y.
  Proof.
    unfold lt; intros (a, b) (a', b') hl he; inv he.
    assert (heq  : a' = a') by auto. 
    apply FA.eq_compare_EQ in heq.
    destruct heq as (heq & hc); rewrite hc in hl.
    assert (heq'  : b' = b') by auto. 
    apply FB.eq_compare_EQ in heq'.
    destruct heq' as (heq' & hc'); rewrite hc' in hl.
    contradiction.
  Qed.

  (** Three-way comparison for pairs, comparing first components and breaking ties with [B.compare]. *)
  Definition compare (x y : t) : Compare lt eq x y.
    refine (match x, y with
            | (a, b), (a', b') =>
              match A.compare a a' with
              | LT hl => LT _
              | GT hl => GT _
              | EQ he =>
                match B.compare b b' with
                | LT hl  => LT _
                | GT hl  => GT _
                | EQ he' => EQ _
                end
              end
            end);
      unfold A.eq, B.eq in *; try red; subst; auto.
    - apply FA.lt_compare_LT in hl.
      destruct hl as [hl heq]; rewrite heq; auto.
    - destruct (FA.compare_refl a') as [heq hc]; rewrite hc. 
      apply FB.lt_compare_LT in hl.
      destruct hl as [hl hc']; rewrite hc'; auto.
    - destruct (FA.compare_refl a') as [heq hc]; rewrite hc.
      apply FB.lt_compare_LT in hl.
      destruct hl as [hl hc']; rewrite hc'; auto.
    - apply FA.lt_compare_LT in hl.
      destruct hl as [hl hc]; rewrite hc; auto.
  Defined.

  (** Decidable equality for pairs, delegating to [A.eq_dec] then [B.eq_dec]. *)
  Definition eq_dec (x y : t) : {x = y} + {x <> y}.
    refine (match x, y with
            | (a, b), (a', b') =>
              match A.eq_dec a a' with
              | left _ =>
                match B.eq_dec b b' with
                | left _  => left _
                | right _ => right _
                end
              | right _ => right _
              end
            end);
      unfold A.eq, B.eq in *; tc.
  Defined.

End PairAsUOT.
  
(** [nat] as an [OrderedTypeAlt], obtained by converting the stdlib [Nat_as_OT] to the alternative interface. *)
Module NatAsOTAlt <: OrderedTypeAlt := OrderedType_to_Alt Nat_as_OT.
