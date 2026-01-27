(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Originally from https://www.cs.cornell.edu/courses/cs6115/2017fa/notes/SimpleLex.v *)
(* Copyright 2017 Cornell University *)
(** * Regular expression matcher based on derivatives, inspired by the paper
      of Owens, Reppy, and Turon.
*)
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Init.Logic.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Eqdep.
From Corelib Require Import PrimInt63 Uint63Axioms.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatIntStd.

Set Implicit Arguments.

(* Module Type MATCHER_ARG.
  (** Our development will be parameterized over a type of characters that supports
      decidable equality. *)
  Parameter int : Set.
  Parameter char_eq : forall (c1 c2:int), {c1=c2} + {c1<>c2}.
End MATCHER_ARG. *)

(* Module Matcher(MA : MATCHER_ARG).
  Import MA. *)

Module Matcher.

  Definition char_eq : forall (c1 c2:int), {c1=c2} + {c1<>c2}.
  Proof.
    intros x y.
    destruct (eqb x y) eqn:E.
    - left. apply eqb_correct, E.
    - right. intro Hxy. subst y. rewrite eqb_refl in E.
      discriminate.
  Defined.

  (** Regular expression abstract syntax *)
  Inductive regexp : Set :=
  | Any                 : regexp
  | Char (c: int)    : regexp
  | Eps                 : regexp
  | Cat (r1 r2: regexp) : regexp
  | Alt (r1 r2: regexp) : regexp
  | Zero                : regexp
  | Star (r: regexp)    : regexp.

  Definition regexp_eq : forall (r1 r2:regexp), {r1=r2} + {r1<>r2}.
    intros.
    decide equality. apply char_eq.
  Defined.

  (** A simplification tactic used through the development *)
  Ltac mysimp :=
      simpl in * ; intros ;
        repeat match goal with
                 | [ |- context[char_eq ?x ?y] ] => destruct (char_eq x y) ; auto
                 | [ |- _ /\ _ ] => split
                 | [ H : existT ?f ?t ?x = existT ?f ?t ?y |- _ ] =>
                   generalize (inj_pairT2 _ f t x y H) ; clear H ; intro H ; subst
                 | [ H : _ /\ _ |- _ ] => destruct H
                 | [ |- context[ _ ++ nil ] ] => rewrite -> app_nil_r
                 | [ H : exists x, _ |- _ ] => destruct H
                 | [ H : _ \/ _ |- _] => destruct H
                 | [ H : _ <-> _ |- _] => destruct H
                 | [ |- _ <-> _ ] => split
                 | [ H : _::_ = _::_ |- _] => injection H ; clear H
                 | _ => idtac
               end ; try (firstorder) ; auto.
  (** Simplification followed by substitution. *)
  Ltac s := repeat (mysimp ; subst).

  (** ** Semantics for [regexp] *)
  (** Now we can give a semantic interpretation to the regexps.  In essence,
      we are giving an interpretation as (inductively-generated) sets of
      strings.  The notation is meant to suggest "Oxford" brackets, but is
      probably an unfortunate choice as it conflicts with the Ltac notation. *)
  Reserved Notation "[[ r ]]" (at level 0).

  Inductive in_regexp : regexp -> list int -> Prop :=
  | Any_i : forall c, [[ Any ]] (c::nil)
  | Char_i : forall c, [[ Char c ]] (c::nil)
  | Eps_i : [[ Eps ]] nil
  | Alt_left_i : forall (r1 r2:regexp) cs,
    [[ r1 ]] cs -> [[ Alt r1 r2 ]] cs
  | Alt_right_i : forall (r1 r2:regexp) cs,
    [[ r2 ]] cs -> [[ Alt r1 r2 ]] cs
  | Cat_i : forall (r1 r2:regexp) cs1 cs2,
    [[ r1 ]] cs1 -> [[ r2 ]] cs2 -> [[ Cat r1 r2 ]] (cs1++cs2)
  | Star_eps_i : forall (r:regexp), [[ Star r ]] nil
  | Star_cat_i : forall (r:regexp) cs1 cs2,
    [[ r ]] cs1 -> [[ Star r ]] cs2 -> [[ Star r ]] (cs1++cs2)
  where "[[ r ]]" := (in_regexp r).
  Hint Constructors in_regexp : dfa.

  (** Equivalence of regular expression parsers. *)
  Definition reg_eq (r1 r2: regexp) : Prop := forall cs, [[r1]] cs <-> [[r2]] cs.
  Infix "[=]" := reg_eq (right associativity, at level 85).

  (** Reflexivity *)
  Lemma reg_eq_refl : forall (r:regexp), r [=] r.
    unfold reg_eq. tauto.
  Qed.
  Hint Resolve reg_eq_refl : dfa.

  (** Transitivity *)
  Lemma reg_eq_trans : forall (r1 r2 r3: regexp), r1 [=] r2 -> r2 [=] r3 -> r1 [=] r3.
    unfold reg_eq. mysimp.
  Qed.

  (** Symmetry *)
  Lemma reg_eq_sym : forall (r1 r2: regexp), r1 [=] r2 -> r2 [=] r1.
    unfold reg_eq ; mysimp.
  Qed.

  Ltac in_inv :=
    match goal with
      | [ H : in_regexp Any _ |- _] => inversion H ; clear H
      | [ H : in_regexp (Char _) _ |- _ ] => inversion H ; clear H ; subst ; mysimp
      | [ H : in_regexp Eps _ |- _] => inversion H ; clear H
      | [ H : in_regexp Zero _ |- _] => inversion H
      | [ H : in_regexp (Cat _ _) _ |- _] => inversion H ; clear H
      | [ H : in_regexp (Alt _ _) _ |- _] => inversion H ; clear H
    end ; subst.

  (** A little tactic that tries to prove [in_regexp]. *)
  Ltac pv_in :=
    try in_inv ;
    match goal with
      | [ |- in_regexp (Cat _ _) (_ ++ _) ] => apply Cat_i ; auto
      | [ |- in_regexp (Cat _ _) nil ] =>
        let H := fresh "H" in
          assert (H:@nil int= nil ++ nil) ; [auto | rewrite H] ; clear H ;
            apply Cat_i ; auto with dfa
      | [ |- in_regexp (Cat _ _) (?c :: ?x ++ ?y) ] =>
        let H := fresh "H" in assert (H: c::x++y = (c::x) ++ y) ;
          [ auto | rewrite H] ; clear H ;
          apply Cat_i ; auto with dfa
      | _ => auto with dfa
    end.

  (** [Cat r Eps] is equivalent to [r] *)
  Lemma cat_eps_r : forall r, (Cat r Eps) [=] r.
  Proof.
    unfold reg_eq ; repeat (mysimp ; pv_in). rewrite <- (app_nil_r cs). repeat pv_in.
  Qed.

  (** [Cat Eps r] is equivalent to [r] *)
  Lemma cat_eps_l : forall r, (Cat Eps r) [=] r.
    unfold reg_eq ; repeat (mysimp ; pv_in). rewrite <- (app_nil_l cs). repeat pv_in.
  Qed.

  (** [Cat r Zero] is equivalent to [Zero] *)
  Lemma cat_zero_r : forall r, (Cat r Zero) [=] Zero.
    unfold reg_eq ; repeat (mysimp ; pv_in).
  Qed.

  (** [Cat Zero r] is equivalent to [Zero] *)
  Lemma cat_zero_l : forall r, (Cat Zero r) [=] Zero.
    unfold reg_eq ; repeat (mysimp ; pv_in).
  Qed.

  (** An optimized constructor for [Cat]. *)
  Definition OptCat (r1 r2: regexp) :=
    match r1, r2 with
      | Zero, _ => Zero
      | Eps, r2 => r2
      | _, Zero => Zero
      | r1, Eps => r1
      | r1, r2 => Cat r1 r2
    end.

  Lemma opt_cat : forall r1 r2, OptCat r1 r2 [=] Cat r1 r2.
    intros. apply reg_eq_sym ;
    destruct r1 ; intros ; simpl ;
      (apply cat_zero_l || apply cat_eps_l || idtac) ;
      destruct r2 ; simpl ;
        (apply cat_zero_r || apply cat_eps_r || apply reg_eq_refl).
  Qed.

  (** [Alt r Zero] is equivalent to [r]. *)
  Lemma alt_zero_r : forall r, (Alt r Zero) [=] r.
    unfold reg_eq ; intros ; mysimp ; repeat pv_in.
  Qed.

  (** [Alt Zero r] is equivalent to [r]. *)
  Lemma alt_zero_l : forall r, (Alt Zero r) [=] r.
    unfold reg_eq ; intros ; mysimp ; repeat pv_in.
  Qed.

  (** [Alt r r] is equivalent to [r]. *)
  Lemma alt_r_r : forall r, (Alt r r) [=] r.
    unfold reg_eq ; intros ; mysimp ; repeat pv_in.
  Qed.

  (** Optimized version of [Alt]. *)
  Definition OptAlt (r1 r2:regexp) : regexp :=
    match r1, r2 with
      | Zero, r2 => r2
      | r1, Zero => r1
      | r1, r2 => if regexp_eq r1 r2 then r1 else Alt r1 r2
    end.

  (** [OptAlt r1 r2] is equivalent to [Alt r1 r2] *)
  Lemma opt_alt : forall r1 r2, OptAlt r1 r2 [=] Alt r1 r2.
    intros. apply reg_eq_sym.
    destruct r1 ; (apply alt_zero_l || idtac) ;
      destruct r2 ; (apply alt_zero_r || apply alt_r_r || apply reg_eq_refl || idtac) ;
    match goal with
      | [ |- _ [=] OptAlt (Char ?c1) (Char ?c2)] =>
        simpl ; destruct (regexp_eq (Char c1) (Char c2));
          destruct (char_eq c1 c2) ; subst ; simpl ;
            try apply alt_r_r ; apply reg_eq_refl
      | [ |- _ [=] OptAlt (_ ?r1 ?r2) (_ ?r3 ?r4) ] =>
        simpl ; destruct (regexp_eq r1 r3) ; subst ;
          try apply reg_eq_refl ;
          destruct (regexp_eq r2 r4) ; subst ; simpl ;
            try apply alt_r_r ; apply reg_eq_refl
      | [ |- _ [=] OptAlt (Star ?r1) (Star ?r2) ] =>
        simpl ; destruct (regexp_eq r1 r2) ; subst ;
          try apply alt_r_r ; apply reg_eq_refl
    end.
  Qed.

  (** ---------------------------------------------------------*)
  (** ** Now we define the actual derivative-based recognizer. *)
  (** ---------------------------------------------------------*)

  (** If [r] accepts the empty string, return Eps, else return Zero. *)
  Fixpoint null (r:regexp) : regexp :=
    match r with
      | Any => Zero
      | Char _ => Zero
      | Eps => Eps
      | Zero => Zero
      | Alt r1 r2 => OptAlt (null r1) (null r2)
      | Cat r1 r2 => OptCat (null r1) (null r2)
      | Star _ => Eps
    end.

  Definition accepts_null (r:regexp) := regexp_eq (null r) Eps.

  (** This is the heart of the algorithm.  It returns a regexp denoting
      { cs | (c::cs) in r }.  *)
  Fixpoint deriv (r:regexp) (c:int) : regexp :=
    match r with
      | Any => Eps
      | Char c' => if char_eq c c' then Eps else Zero
      | Eps => Zero
      | Zero => Zero
      | Alt r1 r2 => OptAlt (deriv r1 c) (deriv r2 c)
      | Cat r1 r2 => OptAlt (OptCat (deriv r1 c) r2) (OptCat (null r1) (deriv r2 c))
      | Star r => OptCat (deriv r c) (Star r)
    end.

  (** This calculates the derivative of a regular expression with respect to a string. *)
  Fixpoint derivs (r:regexp) (cs:list int) : regexp :=
    match cs with
      | nil => r
      | c::cs' => derivs (deriv r c) cs'
    end.

  (** To see if [cs] matches [r], calculate the derivative of [r] with respect
      to [s], and see if the resulting regexp accepts the empty string. *)
  Definition deriv_parse r cs :=
    if accepts_null (derivs r cs) then true else false.

  (** Tactic for helping to reason about the optimizing constructors. *)
  Ltac pv_opt :=
    match goal with
      | [ |- in_regexp (OptAlt ?r1 ?r2) ?cs ] =>
        apply (proj2 (opt_alt r1 r2 cs))
      | [ |- in_regexp (OptCat ?r1 ?r2) ?cs ] =>
        apply (proj2 (opt_cat r1 r2 cs))
      | [ H : ?x ++ ?y = nil |- _] =>
        generalize (app_eq_nil _ _ H) ; clear H ; mysimp
      | [ H : nil = ?x ++ ?y |- _] =>
        generalize (app_eq_nil _ _ (eq_sym H)) ; clear H ; mysimp
      | [ H : in_regexp (OptCat ?r1 ?r2) ?cs |- _] =>
        generalize (proj1 (opt_cat r1 r2 cs) H) ; clear H ; intro H
      | [ H : in_regexp (OptAlt ?r1 ?r2) ?cs |- _] =>
        generalize (proj1 (opt_alt r1 r2 cs) H) ; clear H ; intro H
      | [ H : (_,_) = (_,_) |- _ ] => injection H ; clear H ; mysimp
      | [ H : ?cs1 ++ ?cs2 = ?c :: ?cs |- _ ] =>
        destruct cs1 ; simpl in H ; subst ; [ idtac | injection H ; intros ; subst ]
      | _ => eauto with dfa
    end.

  (** Useful for some rewriting steps below. *)
  Lemma app_nil_beg : forall A (cs:list A), cs = nil ++ cs.
    auto.
  Qed.

  Lemma app_cons : forall A (x:A) (y z:list A), x :: y ++ z = (x::y) ++ z.
    auto.
  Qed.

  (** [r] accepts the empty string iff [null r] accepts the empty string. *)
  Lemma Null1 : forall r, [[r]] nil -> [[null r]] nil.
    induction r ; simpl ; intros ; repeat (in_inv ; pv_opt) ; eauto with dfa ;
      pv_opt ; subst ; auto with dfa.
  Qed.
  Hint Resolve Null1 : core.

  Lemma Null2 : forall r, [[null r]] nil -> [[r]] nil.
    induction r ; simpl ; intros ; repeat in_inv ; repeat pv_opt ; repeat in_inv ;
      eauto with dfa ; pv_opt ; subst ; eauto with dfa.
  Qed.
  Hint Resolve Null2 : core.

  (** If [null r] matches [cs], then [cs] must be empty *)
  Lemma NullNil : forall r cs, [[null r]] cs -> cs = nil.
  Proof.
    induction r ; simpl ; intros ; try in_inv ; auto ; pv_opt ; try in_inv ; repeat
    match goal with
      | [ IHr : forall cs, in_regexp (null ?r) _ -> _ = _,
          H : in_regexp (null ?r) _ |- _] =>
        rewrite (IHr _ H) ; clear IHr ; auto
    end.
  Qed.

  (** [deriv] is correct part 1. *)
  Lemma Deriv1 : forall r c cs, [[r]] (c::cs) -> [[deriv r c]] cs.
  Proof.
    induction r ; simpl ; intros ; (repeat in_inv) ; (repeat pv_opt) ;
    match goal with
      | [ H : in_regexp _ nil |- in_regexp (Alt _ _) ?cs ] =>
        apply Alt_right_i ; rewrite (app_nil_beg cs)
      | [ |- in_regexp (Alt _ _) _ ] => apply Alt_left_i
      | [ H : in_regexp (Star _) _ |- _ ] => idtac
    end ; repeat pv_opt.

    remember (Star r) as r1 ; remember (c::cs) as cs1 ;
      generalize Heqr1 Heqcs1 ; clear Heqr1 Heqcs1 ;
        induction H ; intros ; try congruence ;
    injection Heqr1 ; intros ; subst ; destruct cs1 ; simpl in * ; subst ;
      [eapply IHin_regexp2 ; auto | injection Heqcs1 ; intros ; subst; auto with dfa].
  Qed.

  (** [deriv] is correct part 2. *)
  Lemma Deriv2 : forall r c cs, [[deriv r c]] cs -> [[r]] (c::cs).
  Proof.
    induction r ; simpl ; intros ; try in_inv ; auto with dfa ;
    repeat match goal with
      | [ H : context[char_eq ?c1 ?c2] |- _ ] =>
        destruct (char_eq c1 c2) ; subst ; try congruence ; in_inv ; auto with dfa
      | [ H1: in_regexp (deriv ?r1 _) _, H2 : in_regexp ?r2 _ |-
          in_regexp (Cat ?r1 ?r2) (_ :: _ ++ _) ] => rewrite app_cons ; auto with dfa
      | [ H1 : in_regexp (null ?r1) _ |- _ ] =>
        generalize (NullNil _ H1) ; intros ; subst ; rewrite app_nil_beg ; auto with dfa
      | [ |- in_regexp (Star _) (_::_++_) ] => rewrite app_cons ; eauto with dfa
      | _ => pv_opt ; in_inv ; auto with dfa
    end.
  Qed.

  (** Same thing except for derivatives of strings. *)
  Lemma Derivs1 cs r : [[derivs r cs]] nil -> [[r]] cs.
  Proof.
    revert r.
    induction cs as [| c cs' IH]; intros r H; simpl in *; auto.
    eapply Deriv2.
    apply (IH (deriv r c)); auto.
  Qed.

  Lemma Derivs2 cs r : [[r]] cs -> [[derivs r cs]] nil.
  Proof.
    revert r.
    induction cs as [| c cs' IH]; intros r H; simpl in *; auto.
    apply (IH (deriv r c)).
    eapply Deriv1; auto.
  Qed.

  (** [null r] returns [Eps] or [Zero] *)
  Lemma NullEpsOrZero : forall r, {null r = Eps} + {null r = Zero}.
    induction r ; simpl ; try (right ; auto; fail) ; try (left ; auto; fail) ;
      destruct IHr1 ; destruct IHr2 ; rewrite e;  rewrite e0 ; simpl ; auto.
  Defined.

  (** If [null r] = [Eps], then [r] accepts the empty string. *)
  Lemma AccNull : forall r, null r = Eps -> [[r]] nil.
  Proof.
    induction r ; simpl ; intros ; try congruence ; auto with dfa.
    destruct (null r1) ; simpl in * ; try congruence ; destruct (null r2) ;
      simpl in * ; try congruence.
    rewrite app_nil_beg. auto with dfa.
    destruct (NullEpsOrZero r1). apply Alt_left_i. auto.
    rewrite e in *. simpl in *. apply Alt_right_i. auto.
  Qed.

  (** Correctness of the derivative matcher part 1 *)
  Lemma DerivParse1 : forall r cs, deriv_parse r cs = true -> [[r]] cs.
  Proof.
    unfold deriv_parse. intros. intros. destruct (accepts_null (derivs r cs)) ;
    try congruence. generalize (AccNull _ e). apply Derivs1.
  Qed.

  (** Correctness of the derivative matcher part 2 *)
  Lemma DerivParse2 : forall r cs, [[r]] cs -> deriv_parse r cs = true.
  Proof.
    intros. unfold deriv_parse. generalize (Derivs2 H).
    intros. generalize (Null1 H0). unfold accepts_null.
    generalize (NullEpsOrZero (derivs r cs)). intros. destruct H1 ;
    rewrite e in *. destruct (regexp_eq Eps Eps) ; try congruence ; auto.
    inversion H2.
  Qed.

  (** From this, we can build a decidable regexp matcher by running
      the derivative-based parser. *)
  Definition parse r cs : {[[r]] cs} + {~[[r]] cs}.
    intros.
    remember (deriv_parse r cs) as b.
    generalize (DerivParse1 r cs).
    generalize (@DerivParse2 r cs).
    intros.
    destruct b. left ; auto.
    right. rewrite <- Heqb in *. intro. generalize (H H1). intro. congruence.
  Defined.

  Definition parse_bool r cs : bool :=
    match parse r cs with
    | left _ => true
    | right _ => false
    end.

  Open Scope int63.
  Definition r1 : regexp := Cat (Star (Char 0)) (Char 1).
  Definition s1 : list int := 0 :: 1 :: nil.
  Definition s2 := 1 :: nil.
  Definition s3 := 0 :: 0 :: 1 :: nil.
  Definition s4 := 0 :: nil.

End Matcher.

Require Crane.Extraction.
Require Crane.Mapping.Std.
Crane Extraction "regexp" Matcher.
(** Exercises:

- Show that (Star (Star r)) is equivalent to (Star r) and incorporate this
  in the optimizations.

- Show that (Star Eps) is equivalent to Eps.

- Following Bob Harper's JFP article, an expression r is "standard" if
  whenever it contains a sub-expression (Star r'), then r' does not
  accept the empty string.  Write a function that converts an arbitrary
  regular expression to an equivalent, standard regular-expression.

- An alternative to our derivative-based matcher is to build one based
  on the list monad.  That is, define an interp function of type
  [regexp -> list int -> list (list int)] with the intution
  that:

   cs2 is in (interp r) (cs1 ++ cs2) iff [[r]] cs1

  That is, [interp r] takes a string as input and matches some first
  portion of that string against [r], returning as output the unconsumed rest of
  the list.  If there are multiple matches, then we'll get multiple
  outputs (hence the output list of lists.)

*)
