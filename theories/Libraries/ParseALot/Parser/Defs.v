(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import FSets FSets.FMapAVL Lia List String.
Require Import CoLoR.Util.FGraph.TransClos.
From Crane.Libraries.ParseALot.Parser Require Import Orders.
From Crane.Libraries.ParseALot.Parser Require Import Tactics.
From Crane.Libraries.ParseALot.Parser Require Import Utils.
From Crane Require Import Extraction.
Import ListNotations.

(* Types of grammar symbols; the user provides these at grammar definition time *)
(** Abstract interface that the user instantiates to fix the terminal/nonterminal types,
    their comparisons, display functions, and semantic types. *)
Module Type SymbolTypes.

  (** Abstract terminal and nonterminal symbol types provided by the user. *)
  Parameters terminal nonterminal : Type.

  (** Three-way comparison on terminals, used to build ordered sets/maps. *)
  Parameter compareT : terminal -> terminal -> comparison.

  (** Correctness of [compareT]: returns [Eq] iff the two terminals are equal. *)
  Parameter compareT_eq :
    forall x y : terminal,
      compareT x y = Eq <-> x = y.

  (** Transitivity of [compareT]: same comparison result is preserved along a chain. *)
  Parameter compareT_trans :
    forall (c : comparison) (x y z : terminal),
      compareT x y = c -> compareT y z = c -> compareT x z = c.

  (** Three-way comparison on nonterminals, used to build ordered sets/maps. *)
  Parameter compareNT : nonterminal -> nonterminal -> comparison.

  (** Correctness of [compareNT]: returns [Eq] iff the two nonterminals are equal. *)
  Parameter compareNT_eq :
    forall x y : nonterminal,
      compareNT x y = Eq <-> x = y.

  (** Transitivity of [compareNT]: same comparison result is preserved along a chain. *)
  Parameter compareNT_trans :
    forall (c : comparison) (x y z : nonterminal),
      compareNT x y = c -> compareNT y z = c -> compareNT x z = c.
  
  (** Display functions for terminals and nonterminals used in error messages. *)
  Parameter showT  : terminal    -> string.
  (** Display function for nonterminals used in error messages. *)
  Parameter showNT : nonterminal -> string.

  (** Semantic type family for terminal symbols (the value produced when matching a token). *)
  Parameter t_semty  : terminal    -> Type.
  (** Semantic type family for nonterminal symbols (the synthesized attribute type). *)
  Parameter nt_semty : nonterminal -> Type.
  
End SymbolTypes.

(* Core definitions, parameterized by grammar symbol types *)
(** Functor containing all parser definitions parameterized over a [SymbolTypes] instance. *)
Module DefsFn (Export Ty : SymbolTypes).

  (* Terminal symbols as a usual ordered type *)

  (** Packs terminal comparison into the [UsualComparableType] interface. *)
  Module TAsUCT <: UsualComparableType.
    Definition t             := terminal.
    Definition compare       := compareT.
    Definition compare_eq    := compareT_eq.
    Definition compare_trans := compareT_trans.
  End TAsUCT.

  (** Derives a [UsualOrderedType] for terminals from [TAsUCT]. *)
  Module TAsUOT <: UsualOrderedType := UOTFromUCT TAsUCT.

  (* Nonterminal symbols as a usual ordered type *)

  (** Packs nonterminal comparison into the [UsualComparableType] interface. *)
  Module NTAsUCT <: UsualComparableType.
    Definition t             := nonterminal.
    Definition compare       := compareNT.
    Definition compare_eq    := compareNT_eq.
    Definition compare_trans := compareNT_trans.
  End NTAsUCT.
    
  (** Derives a [UsualOrderedType] for nonterminals from [NTAsUCT]. *)
  Module NTAsUOT <: UsualOrderedType := UOTFromUCT NTAsUCT.

  (* Equality tests for terminals and nonterminals *)

  (** Decidable equality for terminal symbols. *)
  Definition t_eq_dec  := TAsUOT.eq_dec.
  (** Decidable equality for nonterminal symbols. *)
  Definition nt_eq_dec := NTAsUOT.eq_dec.

  (** Boolean equality test for terminals. *)
  Definition beq_t (a a' : terminal) : bool :=
    match t_eq_dec a' a with
    | left _  => true
    | right _ => false
    end.
  
  (** Boolean equality test for nonterminals. *)
  Definition beq_nt (x x' : nonterminal) : bool :=
    match nt_eq_dec x' x with
    | left _  => true
    | right _ => false
    end.

  (** Injectivity of [existT] for terminal semantic values: equal sigma-types imply equal values. *)
  Lemma t_semty_inj :
    forall (a : terminal) (v v' : t_semty a),
      @existT _ _ a v = @existT _ _ a v'
      -> v = v'.
  Proof.
    intros a v v' heq.
    apply Eqdep_dec.inj_pair2_eq_dec in heq; auto.
    apply t_eq_dec.
  Qed.

  Ltac t_inj :=
    match goal with
    | H : @existT _ _ ?a ?v = @existT _ _ ?a ?v' |- _ =>
      apply t_semty_inj in H; subst
    end.

  (** Coerces a nonterminal semantic value along an equality proof [x = y]. *)
  Definition cast_nt_semty
             (x y : nonterminal)
             (heq : x = y)
             (v   : nt_semty x) : nt_semty y.
    subst; auto.
  Defined.

  (** Casting along a reflexivity proof is the identity. *)
  Lemma cast_nt_semty_refl :
    forall x (heq : x = x) v,
      cast_nt_semty x x heq v = v.
  Proof.
    intros x heq v.
    unfold cast_nt_semty.
    unfold eq_rect_r.
    rewrite <- Eqdep_dec.eq_rect_eq_dec; auto.
    apply nt_eq_dec. 
  Qed.

  (* Finite sets of nonterminals *)

  Module NtSet      := FSetList.Make NTAsUOT.
  Module Export NF  := FSetFacts.Facts NtSet.
  Module Export NP  := FSetProperties.Properties NtSet.
  Module Export NE  := FSetEqProperties.EqProperties NtSet.
  Module Export ND  := FSetDecide.Decide NtSet.
  (* hide an alternative definition of "sum" from NtSet *)
  Definition sum := Datatypes.sum.

  (** Converts a list of nonterminals into a finite set. *)
  Definition from_nt_list (ls : list nonterminal) : NtSet.t :=
    fold_right NtSet.add NtSet.empty ls.

  (** List membership and set membership in [from_nt_list] coincide. *)
  Lemma from_nt_list_in_iff :
    forall (x : nonterminal)
           (l : list nonterminal),
      In x l <-> NtSet.In x (from_nt_list l).
  Proof.
    intros x l; split; intro hi; induction l as [| x' l Ih]; sis; try ND.fsetdec.
    - destruct hi as [hh | ht]; subst; auto.
      + ND.fsetdec.
      + apply Ih in ht; ND.fsetdec.
    - destruct (NF.eq_dec x' x); subst; auto.
      right; apply Ih; ND.fsetdec.
  Qed.

  (* Grammar symbols *)

  (** A grammar symbol is either a terminal [T a] or a nonterminal [NT x]. *)
  Inductive symbol := T  : terminal -> symbol
                    | NT : nonterminal -> symbol.

  (** The semantic value type associated with a grammar symbol: [t_semty a] for terminals, [nt_semty x] for nonterminals. *)
  Definition symbol_semty (s : symbol) : Type :=
    match s with
    | T a  => t_semty  a
    | NT x => nt_semty x
    end.

  (* Symbols as a usual ordered type *)
  (** Packages symbols with a lexicographic order (terminals before nonterminals) for use in ordered collections. *)
  Module SymbolAsUOT <: UsualOrderedType.
    
    Definition t := symbol.

    Definition eq       := @eq symbol.
    Definition eq_refl  := @eq_refl symbol.
    Definition eq_sym   := @eq_sym symbol.
    Definition eq_trans := @eq_trans symbol.

    (** Lexicographic order on symbols: terminals before nonterminals, ordered within each class. *)
    Definition lt (x y : symbol) : Prop :=
      match x, y with
      | T a, T b   => TAsUOT.lt a b
      | T _, NT _  => True
      | NT _, T _  => False
      | NT a, NT b => NTAsUOT.lt a b
      end.

    (** Transitivity of the symbol order. *)
    Lemma lt_trans :
      forall x y z, lt x y -> lt y z -> lt x z.
    Proof.
      unfold lt; intros x y z hlt hlt'; destruct x as [a | a];
        destruct y as [b | b]; destruct z as [c | c]; try contradiction; auto.
      - eapply TAsUOT.lt_trans; eauto.
      - eapply NTAsUOT.lt_trans; eauto.
    Qed.
    
    (** Irreflexivity: [lt] is incompatible with equality. *)
    Lemma lt_not_eq :
      forall x y, lt x y -> ~ x = y.
    Proof.
      unfold lt; intros x y hl heq; destruct x as [a | a];
        destruct y as [b | b]; inv heq; auto.
      - eapply TAsUOT.lt_not_eq; eauto.
      - eapply NTAsUOT.lt_not_eq; eauto.
    Qed.

    (** Three-way comparison for symbols, compatible with [lt] and [eq]. *)
    Definition compare (x y : symbol) : Compare lt eq x y.
      refine (match x as x' return x = x' -> _ with
              | T a =>
                fun he => 
                  match y as y' return y = y' -> _ with
                  | T a' =>
                    fun he' => 
                      match TAsUOT.compare a a' with
                      | LT _ => LT _
                      | GT _ => GT _
                      | EQ _ => EQ _
                      end
                  | NT _ => fun _ => LT _
                  end (eq_refl y)
              | NT b =>
                fun he =>
                  match y as y' return y = y' -> _ with
                  | T _   => fun _ => GT _
                  | NT b' =>
                    fun he' =>
                      match NTAsUOT.compare b b' with
                      | LT _ => LT _
                      | GT _ => GT _
                      | EQ _ => EQ _
                      end
                  end (eq_refl y)
              end (eq_refl x));
        red; unfold TAsUOT.eq in *; unfold NTAsUOT.eq in *; subst; auto.
    Defined.

    (** Decidable equality for symbols. *)
    Definition eq_dec (x y : symbol) : {x = y} + {x <> y}.
      refine (match x as x' return x = x' -> _ with
              | T a =>
                fun he =>
                  match y as y' return y = y' -> _ with
                  | T a' =>
                    fun he' =>
                      match TAsUOT.eq_dec a a' with
                      | left _  => left _
                      | right _ => right _
                      end
                  | NT _ => fun _ => right _
                  end (eq_refl y)
              | NT b =>
                fun he =>
                  match y as y' return y = y' -> _ with
                  | T _   => fun _ => right _
                  | NT b' =>
                    fun he' =>
                      match NTAsUOT.eq_dec b b' with
                      | left _  => left _
                      | right _ => right _
                      end
                  end (eq_refl y)
              end (eq_refl x)); tc.
    Defined.

  End SymbolAsUOT.

  (** Injectivity of [existT] for symbol semantic values: equal sigma-types imply equal values. *)
  Lemma symbol_semty_inj :
    forall (x : symbol) (v v' : symbol_semty x),
      @existT _ _ x v = @existT _ _ x v'
      -> v' = v.
  Proof.
    intros x v v' heq.
    apply Eqdep_dec.inj_pair2_eq_dec in heq; auto.
    apply SymbolAsUOT.eq_dec.
  Qed.

  Ltac s_inj :=
    match goal with
    | H : @existT symbol _ _ _ = @existT symbol _ _ _ |- _ =>
      apply symbol_semty_inj in H; subst
    end.

  (* Sequences of symbols (i.e., production right-hand sides) *)

  (** Ordered type for symbol sequences (production right-hand sides), using list ordering. *)
  Module GammaAsUOT <: UsualOrderedType := ListAsUOT SymbolAsUOT.

  (** Boolean equality test for symbol sequences. *)
  Definition beq_gamma (xs ys : list symbol) : bool :=
    if GammaAsUOT.eq_dec xs ys then true else false.

  (** [beq_gamma] returns true iff the two symbol lists are propositionally equal. *)
  Lemma beq_gamma_eq_iff :
    forall xs ys, beq_gamma xs ys = true <-> xs = ys.
  Proof.
    unfold beq_gamma; split; intros; dms; tc. 
  Qed.

  (** The semantic value type for a list of symbols: a heterogeneous tuple of per-symbol types. *)
  Definition symbols_semty (gamma : list symbol) : Type :=
    tuple (List.map symbol_semty gamma).

  (** Coerces a [symbols_semty] value along an equality proof between symbol lists. *)
  Definition cast_ss
             (xs  : list symbol)
             (ys  : list symbol)
             (heq : xs = ys)
             (vs  : symbols_semty xs): symbols_semty ys.
    subst; exact vs.
  Defined.

  (** Casting a [symbols_semty] along a reflexivity proof is the identity. *)
  Lemma cast_ss_refl :
    forall xs vs (heq : xs = xs),
      cast_ss xs xs heq vs = vs.
  Proof.
    intros xs vs heq.
    unfold cast_ss.
    unfold eq_rect_r.
    rewrite <- Eqdep_dec.eq_rect_eq_dec; auto.
    apply GammaAsUOT.eq_dec.
  Qed.

  (** Transfers a property from [vs] to the cast value [vs'] when they are equal up to cast. *)
  Lemma cast_ss_prop_eq :
    forall (xs ys : list symbol)
           (heq   : xs = ys)
           (vs    : symbols_semty xs)
           (vs'   : symbols_semty ys)
           (heq'  : vs' = cast_ss xs ys heq vs)
           (P     : forall (xs : list symbol) (vs : symbols_semty xs), Prop),
      P xs vs -> P ys vs'.
  Proof.
    intros xs ys ? vs vs' ? P hp; subst.
    rewrite cast_ss_refl; auto.
  Qed.

  (** Transitivity of cast: casting in two steps is the same as casting directly. *)
  Lemma cast_ss_ins_trans :
    forall xs ys zs (heq : xs = zs) (heq' : ys = zs) (heq'' : xs = ys) vs,
      cast_ss xs zs heq vs = cast_ss ys zs heq' (cast_ss xs ys heq'' vs).
  Proof.
    intros xs ys zs ? ? ? vs; subst.
    repeat rewrite cast_ss_refl; auto.
  Qed.

  (** Casting there and back again is the identity. *)
  Lemma cast_ss_roundtrip :
    forall xs ys (heq : xs = ys) (heq' : ys = xs) vs,
      cast_ss ys xs heq' (cast_ss xs ys heq vs) = vs.
  Proof.
    intros xs ys heq heq' vs; subst.
    repeat rewrite cast_ss_refl; auto.
  Qed.

  (** Casting a cons-tuple peels the head off and casts only the tail. *)
  Lemma cast_ss_cons :
    forall x ys zs (heq : (x :: ys) = (x :: zs)) v (vs : symbols_semty ys),
      (exists (heq' : ys = zs),
          cast_ss (x :: ys) (x :: zs) heq (v, vs) =
          (v, cast_ss ys zs heq' vs)).
  Proof.
    intros x ys zs heq v vs.
    pose proof heq as heq'; inv heq'.
    exists eq_refl.
    repeat rewrite cast_ss_refl; auto.
  Qed.

  (** If [vs'] is [vs] cast along [xs = ys], then casting both to [zs] gives the same result. *)
  Lemma cast_elim_common :
    forall xs ys zs (heq : xs = zs) (heq' : ys = zs) (heq'' : xs = ys) vs vs',
      vs' = cast_ss _ _ heq'' vs
      -> cast_ss _ _ heq vs = cast_ss _ _ heq' vs'.
  Proof.
    intros xs ys zs heq heq' heq'' vs vs' heq'''; subst.
    repeat rewrite cast_ss_refl; auto.
  Qed.
  
  (** Injectivity of [existT] for [symbols_semty]: equal sigma-types imply equal tuples. *)
  Lemma symbols_semty_inj :
    forall (ys : list symbol) (vs vs' : symbols_semty ys),
      @existT _ _ ys vs' = @existT _ _ ys vs
      -> vs' = vs.
  Proof.
    intros ys vs vs' heq.
    apply Eqdep_dec.inj_pair2_eq_dec in heq; auto.
    apply GammaAsUOT.eq_dec.
  Qed.

  Ltac ss_inj :=
    match goal with
    | H : @existT (list symbol) _ ?ys ?vs = @existT (list symbol) _ ?ys ?vs' |- _ =>
      apply symbols_semty_inj in H; subst
    end.
  
  (** Base case for [concat_tuple]: when [xs] is empty, the concatenation is just [vs']. *)
  Definition concat_tuple_nil_case :
    forall (xs ys : list symbol)
           (vs    : symbols_semty xs)
           (vs'   : symbols_semty ys)
           (heq   : xs = []),
      symbols_semty (xs ++ ys).
    intros xs ys vs vs' heq; subst; auto.
  Defined.

  (** Recursive case for [concat_tuple]: prepends the head value and recurses on the tail. *)
  Definition concat_tuple_rec_case :
    forall (x         : symbol)
           (xs' xs ys : list symbol)
           (vs        : symbols_semty xs)
           (vs'       : symbols_semty ys)
           (f         : forall xs ys, symbols_semty xs -> symbols_semty ys -> symbols_semty (xs ++ ys))
           (heq       : xs = x :: xs'),
      symbols_semty (xs ++ ys).
    intros x xs' xs ys vs vs' f heq; subst.
    destruct vs as (v, vs).
    unfold symbols_semty; constructor.
    - exact v.
    - apply f; auto.
  Defined.
  
  (** Concatenates two heterogeneous semantic-value tuples, analogous to list append. *)
  Fixpoint concat_tuple
             (xs ys : list symbol)
             (vs    : symbols_semty xs)
             (vs'   : symbols_semty ys) : symbols_semty (xs ++ ys) :=
    match xs as xs' return xs = xs' -> _ with
    | []  =>
      fun heq =>
        concat_tuple_nil_case xs ys vs vs' heq
    | x :: xs' =>
      fun heq =>
        concat_tuple_rec_case x xs' xs ys vs vs' concat_tuple heq
    end eq_refl.

  Ltac unct :=
    try unfold concat_tuple_nil_case in *;
    try unfold concat_tuple_rec_case in *;
    try unfold eq_rect_r            in *; sis.

  (** Casting a snoc-tuple distributes: the cast only affects the initial segment. *)
  Lemma cast_ss_snoc :
    forall ys zs x (heq : ys ++ [x] = zs ++ [x]) (vs : symbols_semty ys) (v : symbol_semty x),
      (exists heq' : ys = zs,
          cast_ss (ys ++ [x]) (zs ++ [x]) heq (concat_tuple ys [x] vs (v, tt)) =
          concat_tuple zs [x] (cast_ss ys zs heq' vs) (v, tt)).
  Proof.
    intros ys zs x heq vs v.
    pose proof heq as heq'.
    apply app_inj_tail in heq'.
    destruct heq'; subst.
    exists eq_refl.
    repeat rewrite cast_ss_refl; auto.
  Qed.

  (* Why does rewriting the goal not work at the end of this proof? *)
  (** Concatenating with an empty right tuple is the same as the original value (up to cast). *)
  Lemma concat_tuple_nil_r :
    forall xs vs (heq : xs = xs ++ []),
      concat_tuple xs [] vs tt = cast_ss _ _ heq vs.
  Proof.
    intros xs; induction xs as [| x xs IH]; intros vs heq; sis.
    - destruct vs.
      rewrite cast_ss_refl; auto.
    - destruct vs as (v, vs).
      unfold concat_tuple_rec_case.
      unfold eq_rect_r; sis.
      pose proof (cast_ss_cons x xs (xs ++ []) heq v vs) as hc.
      destruct hc as [heq' heq''].
      rewrite <- IH in heq''; auto.
  Qed.

  (** Associativity of [concat_tuple]: grouping on the left vs. right gives equal results up to cast. *)
  Lemma concat_tuple_assoc :
    forall xs ys zs (heq : (xs ++ ys) ++ zs = xs ++ ys ++ zs) vs vs' vs'',
      concat_tuple xs (ys ++ zs) vs (concat_tuple ys zs vs' vs'') =
      cast_ss ((xs ++ ys) ++ zs) (xs ++ ys ++ zs) heq (concat_tuple (xs ++ ys) zs (concat_tuple xs ys vs vs') vs'').
  Proof.
    intros xs; induction xs as [| x xs IH]; intros ys zs heq vs vs' vs''; sis.
    - destruct vs.
      unfold concat_tuple_nil_case.
      unfold eq_rect_r; sis.
      rewrite cast_ss_refl; auto.
    - destruct vs as (v, vs).
      unfold concat_tuple_rec_case.
      unfold eq_rect_r; sis.
      pose proof (cast_ss_cons x ((xs ++ ys) ++ zs) (xs ++ ys ++ zs) heq v
                               (concat_tuple (xs ++ ys) zs (concat_tuple xs ys vs vs') vs'')) as hc.
      destruct hc as [heq' heq''].
      rewrite <- IH in heq''; auto.
  Qed.

  (** Flipped variant of [concat_tuple_assoc]: right grouping to left grouping up to cast. *)
  Lemma concat_tuple_assoc' :
    forall xs ys zs (heq : xs ++ ys ++ zs = (xs ++ ys) ++ zs) vs vs' vs'',
      concat_tuple (xs ++ ys) zs (concat_tuple xs ys vs vs') vs'' =
      cast_ss (xs ++ ys ++ zs) ((xs ++ ys) ++ zs) heq (concat_tuple xs (ys ++ zs) vs (concat_tuple ys zs vs' vs'')).
  Proof.
    intros xs ys zs heq vs vs' vs''.
    assert (heq' : (xs ++ ys) ++ zs = xs ++ ys ++ zs) by apps.
    rewrite concat_tuple_assoc with (heq := heq').
    rewrite cast_ss_roundtrip; auto.
  Qed.

  (** Congruence for [concat_tuple]: equal (up to cast) inputs give equal (up to cast) concatenations. *)
  Lemma concat_tuple_eq :
    forall xs xs' ys ys' (heq : xs = xs') (heq' : ys = ys') (heq'' : xs ++ ys = xs' ++ ys') vx vx' vy vy',
      vx' = cast_ss xs xs' heq vx
      -> vy' = cast_ss ys ys' heq' vy
      -> concat_tuple xs' ys' vx' vy' = cast_ss _ _ heq'' (concat_tuple xs ys vx vy).
  Proof.
    intros xs xs' ys ys' heq heq' heq'' vx vx' vy vy' h h'; subst.
    repeat rewrite cast_ss_refl; auto.
  Qed.

  (** A singleton-cons concatenation equals the direct pair, up to the obvious cast. *)
  Lemma concat_tuple_cons_app_singleton :
    forall x xs v vs (heq : [x] ++ xs = x :: xs),
      (v, vs) = cast_ss _ _ heq (concat_tuple [x] xs (v, tt) vs).
  Proof.
    intros x xs v vs heq; sis.
    repeat unct.
    rewrite cast_ss_refl; auto.
  Qed.

  (** Shifting a symbol from the right segment to the left segment of a concat is equal up to cast. *)
  Lemma concat_tuple_shift_head_l :
    forall s xs ys (heq : (xs ++ [s]) ++ ys = xs ++ s :: ys) v vs vs',
      concat_tuple xs (s :: ys) vs (v, vs') =
      cast_ss _ _ heq (concat_tuple (xs ++ [s]) ys (concat_tuple xs [s] vs (v, tt)) vs').
  Proof.
    intros s xs ys heq v vs vs'.
    erewrite concat_tuple_assoc'; sis.
    repeat unct.
    rewrite cast_ss_roundtrip; auto.
    Unshelve.
    all : apps.
  Qed.

  (*
  Lemma concat_tuple_app_singleton_cons_eq :
    forall xs xs' s ys ys'
           (heq : xs = xs')
           (heq' : ys = ys')
           (heq'' : (xs' ++ [s]) ++ ys' = xs ++ s :: ys)
           vx vx' v v' vy vy',
      vx' = cast_ss xs xs' heq vx
      -> vy' = cast_ss ys ys' heq' vy
      -> v' = cast_
      -> concat_tuple xs (s :: ys) vx (v, vy) = cast_ss _ _ heq'' (concat_tuple (xs' ++ [s]) ys' (concat_tuple xs' [s] vx' (v' ,tt)) vy').

  Proof.
    intros xs xs' s ys ys' heq heq'

   *)
  
  (** Base case for [rev_tuple]: when [xs] is empty, the reversed tuple is [tt]. *)
  Definition rev_tuple_nil_case :
    forall (xs : list symbol)
           (vs : symbols_semty xs)
           (heq : xs = []),
      symbols_semty (rev xs).
    intros; subst; auto.
  Defined.

  (** Recursive case for [rev_tuple]: snocs the head value onto the recursively reversed tail. *)
  Definition rev_tuple_cons_case :
    forall (xs  : list symbol)
           (x   : symbol)
           (xs' : list symbol)
           (heq : xs = x :: xs')
           (vs  : symbols_semty xs)
           (f   : forall xs, symbols_semty xs -> symbols_semty (rev xs)),
      symbols_semty (rev xs).
    intros xs x xs' heq vs f; subst; sis.
    destruct vs as (v, vs).
    exact (concat_tuple (rev xs') [x] (f xs' vs) (v, tt)).
  Defined.

  (** Reverses a heterogeneous semantic-value tuple, analogous to [List.rev]. *)
  Fixpoint rev_tuple (xs : list symbol) (vs : symbols_semty xs) : symbols_semty (rev xs) :=
    match xs as xs' return xs = xs' -> _ with
    | [] => fun heq => rev_tuple_nil_case xs vs heq 
    | x :: xs' => fun heq => rev_tuple_cons_case xs x xs' heq vs rev_tuple
    end eq_refl.

  Ltac unrt :=
    try unfold rev_tuple_nil_case  in *;
    try unfold rev_tuple_cons_case in *;
    try unfold eq_rect_r          in *; sis.

  (** [rev_tuple] distributes over [concat_tuple]: reversing a concatenation reverses the order of parts. *)
  Lemma rev_tuple_concat_tuple_distr :
    forall xs ys (heq : rev ys ++ rev xs = rev (xs ++ ys)) (vs : symbols_semty xs) (vs' : symbols_semty ys),
      rev_tuple _ (concat_tuple _ _ vs vs') =
      cast_ss _ _ heq (concat_tuple _ _ (rev_tuple _ vs') (rev_tuple _ vs)).
  Proof.
    intros xs; induction xs as [| x xs IH]; intros ys heq vs vs'; sis.
    - destruct vs.
      unfold rev_tuple_nil_case.
      unfold concat_tuple_nil_case.
      unfold eq_rect_r; sis.
      assert (h : rev ys = rev ys ++ []) by auto.
      rewrite concat_tuple_nil_r with (heq := h).
      rewrite cast_ss_roundtrip; auto.
    - destruct vs as (v, vs).
      unfold rev_tuple_cons_case.
      unfold concat_tuple_rec_case.
      unfold eq_rect_r; sis.
      assert (h : (rev ys ++ rev xs) ++ [x] = rev ys ++ rev xs ++ [x]).
      { rewrite <- app_assoc; auto. }
      rewrite concat_tuple_assoc with (heq := h).
      assert (h' : (rev ys ++ rev xs) ++ [x] = rev (xs ++ ys) ++ [x]) by apps.
      rewrite <- cast_ss_ins_trans with (heq := h').
      pose proof cast_ss_snoc as hs.
      specialize (hs (rev ys ++ rev xs) (rev (xs ++ ys)) x h'
                     (concat_tuple _ _ (rev_tuple _ vs') (rev_tuple _ vs)) v).
      destruct hs as [heq' heq''].
      rewrite  heq''.
      rewrite <- IH; auto.
  Qed.

  (** Reversing a snoc-tuple: the snocked element becomes the head of the reversed result. *)
  Lemma rev_tuple_unit :
    forall x xs (heq : x :: rev xs = rev (xs ++ [x])) v vs,
      rev_tuple (xs ++ [x]) (concat_tuple xs [x] vs (v, tt)) =
      cast_ss (x :: rev xs) (rev (xs ++ [x])) heq (v, rev_tuple _ vs).
  Proof.
    intros x xs heq v vs.
    apply rev_tuple_concat_tuple_distr.
  Qed.
  
  (** Reversing twice returns the original tuple, up to the [rev_involutive] cast. *)
  Lemma rev_tuple_involutive :
    forall xs (heq : xs = rev (rev xs)) (vs : symbols_semty xs),
      rev_tuple _ (rev_tuple _ vs) = cast_ss xs (rev (rev xs)) heq vs.
  Proof. intros xs.
    induction xs as [| x xs IH]; intros heq vs; sis.
    - destruct vs.
      unfold cast_ss.
      unfold eq_rect_r.
      rewrite <- Eqdep_dec.eq_rect_eq_dec.
      + unfold rev_tuple_nil_case.
        unfold eq_rect_r.
        rewrite <- Eqdep_dec.eq_rect_eq_dec; auto.
        apply GammaAsUOT.eq_dec.
      + apply GammaAsUOT.eq_dec.
    - destruct vs.
      unfold rev_tuple_cons_case.
      unfold eq_rect_r; sis.
      assert (heq' : x :: rev (rev xs) = rev (rev xs ++ [x])).
      { rewrite rev_unit; auto. }
      rewrite rev_tuple_unit with (xs := rev xs) (heq := heq').
      assert (heq'' : x :: xs = x :: rev (rev xs)).
      { rewrite rev_involutive; auto. }
      rewrite cast_ss_ins_trans with
          (heq := heq) (heq' := heq') (heq'' := heq'').
      pose proof cast_ss_cons as hc.
      specialize (hc x xs (rev (rev xs)) heq'' s t).
      destruct hc as [heq4 heq5].
      rewrite IH with (heq := heq4).
      rewrite <- heq5; auto.
  Qed.

  (** Utility: [xs = rev (rev xs) ++ []], used to reshape goals for [rrt_anr]. *)
  Lemma rr_anr_expand :
    forall A (xs : list A),
      xs = rev (rev xs) ++ [].
  Proof.
    intros.
    rew_anr.
    rewrite rev_involutive; auto.
  Qed.

  (** Utility: [xs = rev (rev xs)], a trivial reformulation of [rev_involutive]. *)
  Lemma rr_expand :
    forall A (xs : list A),
      xs = rev (rev xs).
  Proof.
    intros A xs.
    rewrite rev_involutive; auto.
  Qed.

  (** Utility: [xs = xs ++ []], i.e., appending nil on the right is identity. *)
  Lemma anr_expand :
    forall A (xs : list A),
      xs = xs ++ [].
  Proof.
    intros; apps.
  Qed.
  
  (** Double-reverse then nil-append equals the original tuple up to the combined cast. *)
  Lemma rrt_anr :
    forall xs vs (heq : xs = rev (rev xs) ++ []),
      concat_tuple _ [] (rev_tuple _ (rev_tuple _ vs)) tt =
      cast_ss xs (rev (rev xs) ++ []) heq vs.
  Proof.
    intros xs vs heq.
    rewrite concat_tuple_nil_r with (heq := anr_expand _ (rev (rev xs))).
    rewrite rev_tuple_involutive with (heq := rr_expand _ xs).
    erewrite <- cast_ss_ins_trans; eauto.
  Qed.
  
  (* Grammar productions *)

  (** A grammar production is a pair of a left-hand-side nonterminal and a right-hand-side symbol list. *)
  Definition production := (nonterminal * list symbol)%type.

  (** Ordered type for productions, using the lexicographic product of NT and Gamma orders. *)
  Module ProductionAsUOT <: UsualOrderedType := PairAsUOT NTAsUOT GammaAsUOT.

  (* Finite maps with productions as keys *)
  Module PM  := FMapAVL.Make ProductionAsUOT.
  Module PMF := FMapFacts.Facts PM.
  Crane NoArena PM.Raw.tree.

  (** A [MapsTo] witness implies [In] for production finite maps. *)
  Lemma pm_mapsto_in :
    forall (p : production)
           (A : Type)
           (a : A)
           (m : PM.t A),
      PM.MapsTo p a m -> PM.In p m.
  Proof.
    intros x A a m hm.
    apply PMF.in_find_iff.
    intros hf.
    apply PMF.find_mapsto_iff in hm; tc.
  Qed.

  (** The [PM.eq_key_elt] relation on production maps is an equivalence relation. *)
  Lemma grammar_eq_key_elt_equivalence :
    forall (A : Type),
      Equivalence (PM.eq_key_elt (elt:=A)).
  Proof.
    constructor; try firstorder.
    - intros x y z heq heq'.
      repeat red in heq; repeat red in heq'; repeat red.
      destruct heq as [h1 h2]; destruct heq' as [h3 h4].
      rewrite h1; rewrite h3; rewrite h2; rewrite h4; auto.
  Qed.

  (** [InA] under [PM.eq_key_elt] implies ordinary list [In] for productions. *)
  Lemma pm_in_a__in :
    forall A x ys e prs,
      InA (PM.eq_key_elt (elt:=A)) ((x, ys), e) prs
      -> In ((x, ys), e) prs.
  Proof.
    intros A x ys e prs hi; induction prs as [| ((x', ys'), e') prs Ih]; sis.
    - inv hi.
    - inversion hi as [pr' prs' heq | pr' prs' hi']; subst; clear hi.
      + repeat red in heq; sis.
        destruct heq as [heq ?]; subst.
        inv heq; auto.
      + right; auto.
  Qed.

  Ltac mapsto_fun heq :=
    match goal with
    | H : PM.MapsTo ?k ?v ?m, H' : PM.MapsTo ?k ?v' ?m |- _ =>
      assert (heq : v = v') by (eapply PMF.MapsTo_fun in H; eauto)
    end.

  (** Extracts the left-hand-side nonterminal from a production. *)
  Definition lhs' (p : production) : nonterminal :=
    let (x, _) := p in x.

  (** Returns the list of all left-hand-side nonterminals from a list of productions. *)
  Definition lhss' (ps : list production) : list nonterminal :=
    map lhs' ps.

  (** If [(x, ys)] is in a production list, then [x] appears in its LHS list. *)
  Lemma production_lhs_in_lhss' :
    forall ps x ys,
      In (x, ys) ps
      -> In x (lhss' ps).
  Proof.
    intros ps x ys hi.
    apply in_map_iff.
    exists (x, ys); split; sis; auto.
  Qed.

  (** If a nonterminal appears in the LHS list, it has a corresponding RHS in the production list. *)
  Lemma in_lhss'_exists_rhs :
    forall x ps,
      In x (lhss' ps)
      -> exists ys,
        In (x, ys) ps.
  Proof.
    intros x ps hi.
    apply in_map_iff in hi.
    destruct hi as [(x', ys) [? hi]]; sis; subst; eauto.
  Qed.

  (** Extracts the right-hand-side symbol list from a production. *)
  Definition rhs' (p : production) : list symbol :=
    let (_, gamma) := p in gamma.

  (** Returns the list of all right-hand sides from a list of productions. *)
  Definition rhss' (ps : list production) : list (list symbol) :=
    map rhs' ps.

  (** Collects all right-hand sides for a given nonterminal from a flat production list. *)
   Fixpoint rhss_for' (ps : list production) (x : nonterminal) : list (list symbol) :=
    match ps with
    | []                 => []
    | (x', gamma) :: ps' => 
      if nt_eq_dec x' x then 
        gamma :: rhss_for' ps' x
      else 
        rhss_for' ps' x
    end.
  
  (** A symbol list [ys] is in [rhss_for' ps x] iff [(x, ys)] is in [ps]. *)
  Lemma rhss_for'_in_iff :
    forall ps x ys,
      In ys (rhss_for' ps x)
      <-> In (x, ys) ps.
  Proof.
    intros g x ys; split; intros hi.
    - induction g as [| (x', ys') g]; sis; tc.
      dm; subst; auto.
      inv hi; auto.
    - induction g as [| (x', ys') g]; sis; tc.
      destruct hi as [heq | hi].
      + inv heq.
        dm; tc.
        apply in_eq.
      + dm; subst; auto. 
        apply in_cons; auto.
  Qed.

  Hint Resolve rhss_for'_in_iff : core.

  (** Any RHS appearing under a specific nonterminal also appears in the full RHS list. *)
  Lemma rhss_for'_rhss :
    forall ps x rhs,
      In rhs (rhss_for' ps x) -> In rhs (rhss' ps).
  Proof.
    intros g x rhs Hin; induction g as [| (x', rhs') ps IH]; simpl in *.
    - inv Hin.
    - dm; subst; auto.
      destruct Hin as [Heq | Hin]; subst; auto.
  Qed.

  (** The type of a semantic predicate for a production: maps a tuple of RHS values to a boolean. *)
  Definition predicate_semty (p : production) : Type :=
    let (_, ys) := p in symbols_semty ys -> bool.

  (** Coerces a semantic predicate along a proof that its production equals another. *)
  Definition cast_predicate
             (x y  : production)
             (heq  : x = y)
             (p    : predicate_semty x) : predicate_semty y.
    subst; exact p.
  Defined.

  (** Casting a predicate along a reflexivity proof is the identity. *)
    Lemma cast_predicate_refl :
    forall xs (heq : xs = xs) p,
      cast_predicate xs xs heq p = p.
  Proof.
    intros xs heq p.
    unfold cast_predicate.
    unfold eq_rect_r.
    rewrite <- Eqdep_dec.eq_rect_eq_dec; auto.
    apply ProductionAsUOT.eq_dec.
  Qed.

  (** Transfers a property from [p] to the cast predicate [p'] when they are equal up to cast. *)
  Lemma cast_predicate_prop_eq :
    forall (x y   : production)
           (heq   : x = y)
           (p     : predicate_semty x)
           (p'    : predicate_semty y)
           (heq'  : p' = cast_predicate x y heq p)
           (P     : forall (x : production) (p : predicate_semty x), Prop),
      P x p -> P y p'.
  Proof.
    intros; subst.
    rewrite cast_predicate_refl; auto.
  Qed.

  (** Transitivity of predicate cast: two-step cast equals a direct cast. *)
  Lemma cast_predicate_ins_trans :
    forall x y z (heq : x = z) (heq' : y = z) (heq'' : x = y) p,
      cast_predicate x z heq p = cast_predicate y z heq' (cast_predicate x y heq'' p).
  Proof.
    intros; subst.
    repeat rewrite cast_predicate_refl; auto.
  Qed.

  (** Casting a predicate there and back is the identity. *)
  Lemma cast_predicate_roundtrip :
    forall x y (heq : x = y) (heq' : y = x) p,
      cast_predicate y x heq' (cast_predicate x y heq p) = p.
  Proof.
    intros; subst.
    repeat rewrite cast_predicate_refl; auto.
  Qed.

  (** If predicate [p] holds on [vs], then the cast predicate holds on the corresponding cast values. *)
  Lemma cast_predicate_eq_true :
    forall x ys ys' (heq : ys = ys') (heq' : (x, ys) = (x, ys')) (vs : symbols_semty ys) (vs' : symbols_semty ys') (p : predicate_semty (x, ys)),
      vs' = cast_ss ys ys' heq vs
      -> p vs = true
      -> (cast_predicate (x, ys) (x, ys') heq' p) vs' = true.
  Proof.
    intros x ys ys' heq heq' vs vs' p heq'' hp; subst.
    rewrite cast_predicate_refl.
    rewrite cast_ss_refl; auto.
  Qed.
  
  (** The type of a semantic action for a production: maps RHS values to the LHS nonterminal's semantic type. *)
  Definition action_semty (p : production) : Type :=
    let (x, ys) := p in symbols_semty ys -> nt_semty x.

  (** Coerces a semantic action along a proof that its production equals another. *)
  Definition cast_action
             (x y  : production)
             (heq  : x = y)
             (f    : action_semty x) : action_semty y.
    subst; exact f.
  Defined.

  (** Casting an action along a reflexivity proof is the identity. *)
  Lemma cast_action_refl :
    forall x (heq : x = x) f,
      cast_action x x heq f = f.
  Proof.
    intros xs heq p.
    unfold cast_action.
    unfold eq_rect_r.
    rewrite <- Eqdep_dec.eq_rect_eq_dec; auto.
    apply ProductionAsUOT.eq_dec.
  Qed.

  (** Applying [f] to [vs] equals applying the cast action to the cast values. *)
  Lemma cast_action_eq :
    forall x ys ys' (heq : ys = ys') (heq' : (x, ys) = (x, ys')) (vs : symbols_semty ys) (vs' : symbols_semty ys') (f : action_semty (x, ys)),
      vs' = cast_ss ys ys' heq vs
      -> f vs = (cast_action _ _ heq' f) vs'.
  Proof.
    intros x ys ys' heq heq' vs vs' f heq''; subst.
    rewrite cast_action_refl.
    rewrite cast_ss_refl; auto.
  Qed.
  
  (* Grammars *)

  (* Each grammar production includes a semantic predicate
     and a semantic action. The production's symbols
     determine the types of these functions. *)
  (** The combined semantic type for a production: a pair of predicate and action. *)
  Definition production_semty (p : production) : Type :=
    predicate_semty p * action_semty p.

  (** Coerces a production semantic pair along an equality proof between productions. *)
  Definition cast_production_semty
             (p p' : production)
             (heq  : p = p')
             (fs   : production_semty p) : production_semty p'.
    subst; auto.
  Defined.

  (** A grammar entry is a dependent pair of a production and its corresponding predicate/action pair. *)
  Definition grammar_entry : Type :=
    {p : production & production_semty p}.

  
  (** Injectivity of grammar entries: if two entries are equal then their predicates and actions are equal. *)
  Lemma inv_grammar_entry_eq :
    forall x ys (p p' : predicate_semty (x, ys)) (f f' : action_semty (x, ys)),
      @existT _ production_semty (x, ys) (p, f) = @existT _ production_semty (x, ys) (p', f')
      -> p = p' /\ f = f'.
  Proof.
    intros x ys p p' f f' heq.
    apply Eqdep_dec.inj_pair2_eq_dec in heq; auto.
    - inv heq; auto.
    - apply ProductionAsUOT.eq_dec.
  Qed.
    
  (** A grammar is a finite map from productions to their grammar entries (predicate/action pairs). *)
  Definition grammar : Type :=
    PM.t grammar_entry.

  (** Casting the key and entry of a [MapsTo] fact produces an equivalent [MapsTo] fact. *)
  Lemma mapsto_cast  :
    forall (g        : grammar)
           (x x' y z : production)
           (heq      : x = x')
           (heq'     : y = z)
           (p        : predicate_semty y)
           (f        : action_semty y),
      PM.MapsTo x (@existT _ _ y (p, f)) g
      -> PM.MapsTo x' (@existT _ _ z (cast_predicate y z heq' p, cast_action y z heq' f)) g.
  Proof.
    intros g x x' y z heq heq' p f hm; subst.
    rewrite cast_predicate_refl.
    rewrite cast_action_refl; auto.
  Qed.
    
  (* might not be necessary *)
  (** Holds when nonterminal [x] appears as the LHS of some production in [g]. *)
  Definition lhs_in_grammar (x : nonterminal) (g : grammar) : Prop :=
    exists (ys : list symbol), PM.In (x, ys) g.

  (** The list of all productions in a grammar, obtained from the finite map's element list. *)
  Definition productions (g : grammar) : list production :=
    map fst (PM.elements g).

  (** Map membership and list membership in [productions g] coincide. *)
  Lemma in_productions_iff :
    forall g x ys,
      PM.In (x, ys) g <-> In (x, ys) (productions g).
  Proof.
    intros g x ys; split; intros hi.
    - apply in_map_iff.
      apply PMF.elements_in_iff in hi.
      destruct hi as [e hi].
      apply pm_in_a__in in hi.
      exists ((x, ys), e); auto.
    - apply in_map_iff in hi.
      destruct hi as [((x',ys'), e) [heq hi]]; sis.
      inv heq.
      apply PMF.elements_in_iff.
      exists e.
      apply In_InA; auto.
      apply grammar_eq_key_elt_equivalence.
  Qed.

  (** The list of all left-hand-side nonterminals in a grammar. *)
  Definition lhss (g : grammar) : list nonterminal :=
    map fst (productions g).

  (** Any production in [g] contributes its LHS to [lhss g]. *)
  Lemma production_lhs_in_lhss :
    forall g x ys,
      PM.In (x, ys) g -> In x (lhss g).
  Proof.
    intros g x ys hi.
    apply in_map_iff.
    exists (x, ys).
    split; auto.
    apply in_productions_iff; auto.
  Qed.

  (** The list of all right-hand sides in a grammar. *)
  Definition rhss (g : grammar) : list (list symbol) :=
    map snd (productions g).

  (** The set of all nonterminals that appear as LHS in grammar [g]. *)
  Definition all_nts (g : grammar) : NtSet.t :=
    from_nt_list (lhss g).

  (** List membership in [lhss g] and set membership in [all_nts g] coincide. *)
  Lemma all_nts_lhss_iff :
    forall (g : grammar) (x : nonterminal),
      In x (lhss g)
      <-> NtSet.In x (all_nts g).
  Proof.
    intros g x; split; intros hi; apply from_nt_list_in_iff; auto.
  Qed.
  
  (** Well-formedness of a grammar: for every entry, the stored production equals the map key. *)
  Definition grammar_wf (g : grammar) : Prop :=
    forall p p' fs, PM.MapsTo p (@existT _ _ p' fs) g -> p = p'.

  (* Function for producing a well-formed grammar from a list of grammar entries *)
  (** Builds a grammar finite map from a list of grammar entries by inserting each by its production key. *)
  Fixpoint grammar_of_entry_list (es : list grammar_entry) : grammar :=
    match es with
    | []       => PM.empty grammar_entry
    | e :: es' =>
      match e with
      | @existT _ _ p _ => PM.add p e (grammar_of_entry_list es')
      end
    end.

  (** The grammar produced by [grammar_of_entry_list] is always well-formed. *)
  Lemma grammar_of_entry_list_wf :
    forall es,
      grammar_wf (grammar_of_entry_list es).
  Proof.
    intros es; induction es as [| [p fs] es IH]; sis; red.
    - intros p p' fs hm.
      exfalso. eapply PMF.empty_mapsto_iff; eauto.
    - intros p' p'' fs'' hm.
      destruct (ProductionAsUOT.eq_dec p' p); subst.
      + apply PMF.add_mapsto_iff in hm.
        destruct hm as [[_ heq'] | hneq'].
        * inv heq'; auto.
        * exfalso; destruct hneq' as [hc _]; tc.
      + apply PM.add_3 in hm; auto.
        apply IH in hm; auto.
  Qed.          

(*
  Lemma foo :
    forall (gr : grammar) k k' v,
      grammar_wf gr
      -> PM.MapsTo k v gr
      -> k' = k cast_lookup_result
      -> exists (v' : production_semty k'),
          PM.MapsTo k' (@existT _
  Proof.
    intros gr k k' v hm ?; subst; auto.
  Qed.
   *)
  
  (* A well-formed grammar is essentially a dependent map, 
     where the type of each entry (semantic predicate / 
     semantic action pair) depends on the key (production) 
     associated with it. Coq's standard library for finite
     maps does not provide a dependent interface, so we create
     one as follows:

     A well-formed grammar is a finite map in which keys are
     productions, entries are (production, semantic function)
     pairs, and for each key/entry pair, the productions in the
     key and entry are equal. *)
  (** A well-formed grammar: a grammar paired with its well-formedness proof. *)
  Definition wf_grammar : Type :=
    {g : grammar | grammar_wf g}.

  (*
  Definition cast_predicate_from_lookup :
    forall (gr   : grammar)
           (x y  : production)
           (p    : predicate_semty y)
           (f    : action_semty y)
           (hw   : grammar_wf gr)
           (hm   : PM.MapsTo x (@existT _ _ y (p, f)) gr),
      predicate_semty x.
    intros g x y p f hw hm. 
    apply hw in hm; subst; auto.
  Defined.
   *)
  
  (** Applying [p] to [vs] equals applying the cast predicate to the cast values. *)
  Lemma predicate_appl_eq_cast :
    forall (x : nonterminal)
           (ys ys' : list symbol)
           (vs : symbols_semty ys)
           (p  : predicate_semty (x, ys))
           (heq : (x, ys) = (x, ys'))
           (heq' : ys = ys'),
      p vs = (cast_predicate (x, ys) (x, ys') heq p) (cast_ss ys ys' heq' vs).
  Proof.
    intros x ys ys' vs p heq heq'.
    subst.
    rewrite cast_predicate_refl.
    rewrite cast_ss_refl; auto.
  Qed.

  (** Recovers a [production_semty p] from a [find] result using the well-formedness proof to align the production. *)
  Definition cast_lookup_result :
    forall (gr   : grammar)
           (p p' : production)
           (fs   : production_semty p')
           (hw   : grammar_wf gr)
           (hf   : PM.find p gr = Some (@existT _ _ p' fs)),
      production_semty p.
    intros g p p' fs hw hf.
    apply PMF.find_mapsto_iff in hf.
    apply hw in hf; subst; auto.
  Defined.

  (** When the stored production equals the key, [cast_lookup_result] is the identity. *)
  Lemma cast_lookup_result_refl :
    forall gr p fs fs' hw hf,
      cast_lookup_result gr p p fs hw hf = fs'
      -> fs = fs'.
  Proof.
    intros gr p fs fs' hw hf hc.
    unfold cast_lookup_result in hc.
    unfold eq_rect_r in hc.
    unfold eq_sym in hc.
    rewrite <- Eqdep_dec.eq_rect_eq_dec in hc; auto.
    apply PMF.eq_dec.
  Qed.
  
  (** If [p] is in [g] then [PM.find p g] is not [None]. *)
  Lemma in_find_contra :
    forall (p : production)
           (g : grammar),
      PM.In p g
      -> PM.find p g <> None.
  Proof.
    intros p g hi hf.
    eapply PMF.in_find_iff; eauto.
  Defined.

  (* Look up the semantic predicate and action associated
     with a given production *)
  (** Looks up the predicate/action pair for production [p] in a well-formed grammar, returning [None] if absent. *)
  Definition find_predicate_and_action
             (p  : production)
             (g  : grammar)
             (hw : grammar_wf g) : option (production_semty p) :=
    match PM.find p g as o return PM.find p g = o -> _ with
    | Some (@existT _ _ _ fs) =>
      fun hf =>
        Some (cast_lookup_result _ _ _ fs hw hf)
    | None =>
      fun _ =>
        None
    end eq_refl.

  (** Internal case analysis for [find_predicate_and_action]: reconstructs the [find] result from the output option. *)
  Lemma fpaa_cases' :
    forall (gr  : grammar)
           (hw  : grammar_wf gr)
           (x   : nonterminal)
           (ys  : list symbol)
           (o   : option grammar_entry)
           (heq : PM.find (x, ys) gr = o)
           (o'  : option (production_semty (x, ys))),
      match o as r return PM.find (x, ys) gr = r -> _ with
      | Some (@existT _ _ _ fs) =>
        fun hf =>
          Some (cast_lookup_result _ _ _ fs hw hf)
      | None =>
        fun _ =>
          None
      end heq = o'
      -> match o' with
         | Some (p, f) =>
           PM.find (x, ys) gr = Some (@existT _ _ (x, ys) (p, f))
         | None =>
           PM.find (x, ys) gr = None
         end.
  Proof.
    intros gr hw x ys o hf o' heq.
    pose proof hf as hf'.
    destruct o as [((x', ys'), (p, f)) |]; subst; auto.
    - apply PMF.find_mapsto_iff in hf'.
      apply hw in hf'; inv hf'.
      destruct (cast_lookup_result _ _ _ _ _ _) as (o, f') eqn:hc.
      apply cast_lookup_result_refl in hc; inv hc; auto.
  Qed.

  (** Case analysis on [find_predicate_and_action]: a [Some] means a [find] hit, [None] means a miss. *)
  Lemma fpaa_cases :
    forall (gr  : grammar)
           (hw  : grammar_wf gr)
           (x   : nonterminal)
           (ys  : list symbol)
           (o   : option (production_semty (x, ys))),
      find_predicate_and_action (x, ys) gr hw = o
      -> match o with
         | Some (p, f) =>
           PM.find (x, ys) gr = Some (@existT _ _ (x, ys) (p, f))
         | None =>
           PM.find (x, ys) gr = None
         end.
  Proof.
    intros; eapply fpaa_cases'; eauto.
  Qed.
  
  (** A successful [find_predicate_and_action] lookup implies a [MapsTo] fact in the grammar. *)
  Lemma fpaa_mapsto :
    forall g hw x ys p f,
      find_predicate_and_action (x, ys) g hw = Some (p, f)
      -> PM.MapsTo (x, ys) (@existT _ _ (x, ys) (p, f)) g.
  Proof.
    intros g hw x ys p f hf.
    apply fpaa_cases in hf.
    apply PMF.find_mapsto_iff; auto.
  Qed.

  Ltac appl_fpaa :=
    match goal with
    | H : find_predicate_and_action _ _ _ = Some _ |- _ =>
      apply fpaa_mapsto in H
    end.

  (** If [find_predicate_and_action] returns [None], then the production is absent from the grammar. *)
  Lemma fpaa_none_contra :
    forall gr hw p,
      find_predicate_and_action p gr hw = None
      -> ~ PM.In p gr.
  Proof.
    intros gr hw (x, ys) hf hi.
    eapply in_find_contra; eauto.
    apply fpaa_cases in hf; auto.
  Qed.

  (* An rhs_map maps each grammar nonterminal to its
     right-hand sides. It provides an efficient way to look
     up all right-hand sides for a given nonterminal -- a 
     frequent parser operation. *)
  
  (* Finite maps with nonterminal keys *)
  Module NM  := FMapAVL.Make NTAsUOT.
  Module NMF := FMapFacts.Facts NM.
  Crane NoArena NM.Raw.tree.

  (** A [MapsTo] witness implies [In] for nonterminal finite maps. *)
  Lemma nm_mapsto_in :
    forall (x : nonterminal)
           (A : Type)
           (a : A)
           (m : NM.t A),
      NM.MapsTo x a m -> NM.In x m.
  Proof.
    intros x A a m hm.
    apply NMF.in_find_iff.
    intros hf.
    apply NMF.find_mapsto_iff in hm; tc.
  Qed.

  (** [InA] under [NM.eq_key_elt] implies ordinary list [In] for nonterminal maps. *)
  Lemma nm_in_a_in :
    forall B x (y : B) prs,
      InA (NM.eq_key_elt (elt:=B)) (x, y) prs
      -> In (x, y) prs.
  Proof.
    intros B x y prs hi; induction prs as [| (x', y') prs IH]; inv hi; sis; auto.
    match goal with
    | H : NM.eq_key_elt _ _ |- _ => inv H
    end.
    sis; subst; auto.
  Qed.

  (** The [NM.eq_key_elt] relation on nonterminal maps is an equivalence relation. *)
  Lemma nm_eq_key_elt_equivalence :
    forall (A : Type),
      Equivalence (NM.eq_key_elt (elt:=A)).
  Proof.
    constructor; try firstorder.
    - intros x y z heq heq'.
      repeat red in heq; repeat red in heq'; repeat red.
      destruct heq as [h1 h2]; destruct heq' as [h3 h4].
      rewrite h1; rewrite h3; rewrite h2; rewrite h4; auto.
  Qed.
  
  (** [MapsTo] and list [In] over [NM.elements] coincide for nonterminal maps. *)
  Lemma nm_mapsto_elements_iff :
    forall B x (y : B) m,
      NM.MapsTo x y m <-> In (x, y) (NM.elements m).
  Proof.
    intros B x y m; split; [intros hm | intros hi].
    - apply nm_in_a_in.
      apply NMF.elements_mapsto_iff in hm; auto.
    - apply NMF.elements_mapsto_iff.
      apply In_InA; auto.
      apply nm_eq_key_elt_equivalence.
  Qed.

  (** A successful [NM.find] implies [NM.In]. *)
  Lemma find_some__in :
    forall (x : nonterminal)
           (A : Type)
           (a : A)
           (m : NM.t A),
      NM.find x m = Some a -> NM.In x m.
  Proof.
    intros x A a m hi.
    apply NMF.in_find_iff; tc.
  Qed.

  (** An [rhs_map] maps each nonterminal to its list of right-hand sides, for fast lookup during prediction. *)
  Definition rhs_map := NM.t (list (list symbol)).

  (** Collects every right-hand side stored in an [rhs_map] into a flat list. *)
  Definition all_rhss (rm : rhs_map) : list (list symbol) :=
    List.concat (List.map snd (NM.elements rm)).

  (** Inserts a production's RHS into the [rhs_map] under its LHS nonterminal, creating the list if needed. *)
  Definition add_production
             (p : production)
             (e : grammar_entry)
             (rm : rhs_map) : rhs_map :=
    match p with
    | (x, ys) =>
      match NM.find x rm with
      | Some yss => NM.add x (ys :: yss) rm
      | None     => NM.add x [ys] rm
      end
    end.

  (** Builds an [rhs_map] from a grammar by folding [add_production] over all its entries. *)
  Definition mk_rhs_map (g : grammar) : rhs_map :=
    PM.fold add_production g (NM.empty (list (list symbol))).

  (* Soundness of keys in the result of mk_rhs_map w.r.t. the input grammar *)

  (** Auxiliary invariant: every nonterminal key in [rm] appears as a LHS in [prs]. *)
  Definition rmks' (rm : rhs_map) (prs : list (production * grammar_entry)) : Prop :=
    forall x,
      NM.In x rm -> exists ys e, In ((x, ys), e) prs.
  
  (** The empty [rhs_map] trivially satisfies [rmks']. *)
  Lemma rmks'_empty :
      rmks' (NM.empty (list (list symbol))) [].
  Proof.
    intros x hi.
    apply NMF.empty_in_iff in hi; destruct hi.
  Qed.
  
  (** [add_production] preserves the [rmks'] invariant when extending the production list. *)
  Lemma add_production_preserves_rmks' :
    forall rm pr prs,
      rmks' rm prs
      -> rmks' (add_production (fst pr) (snd pr) rm) (prs ++ [pr]).
  Proof.
    intros rm ((x, ys), e) prs hi x' hi'; red in hi; sis.
    destruct (NM.find x rm) as [yss |] eqn:hf.
    - destruct (nt_eq_dec x' x) as [heq | hneq]; subst.
      + apply find_some__in in hf.
        apply hi in hf.
        destruct hf as [ys' [e' hi'']].
        exists ys', e'.
        apply in_or_app; left; auto.
      + apply NMF.add_neq_in_iff in hi'; auto.
        apply hi in hi'.
        destruct hi' as [ys' [e' hi']].
        exists ys', e'.
        apply in_or_app; left; auto.
    - destruct (nt_eq_dec x' x) as [heq | hneq]; subst.
      + exists ys, e.
        apply in_or_app; right.
        apply in_eq.
      + apply NMF.add_neq_in_iff in hi'; auto.
        apply hi in hi'.
        destruct hi' as [ys' [e' hi']].
        exists ys', e'.
        apply in_or_app; left; auto.
  Qed.
  
  (** Folding [add_production] over [prs] from the empty map satisfies [rmks']. *)
  Lemma rmks'__fold_left :
    forall (prs : list (production * grammar_entry)),
      rmks'
        (fold_left (fun a p => add_production (fst p) (snd p) a)
                   prs
                   (NM.empty (list (list symbol))))
        prs.
  Proof.
    intros prs.
    apply fold_left_preserves_list_invar.
    - apply rmks'_empty.
    - apply add_production_preserves_rmks'.
  Qed.

  (** Every nonterminal key in [rm] is the LHS of some production in [g]. *)
  Definition rhs_map_keys_sound (rm : rhs_map) (g : grammar) : Prop :=
    forall x,
      NM.In x rm -> exists ys, PM.In (x, ys) g.
  
  (** [mk_rhs_map] satisfies [rhs_map_keys_sound] for any grammar. *)
  Lemma mk_rhs_map_keys_sound :
    forall g,
      rhs_map_keys_sound (mk_rhs_map g) g.
  Proof.
    intros g x hi.
    unfold mk_rhs_map in hi.
    rewrite PM.fold_1 in hi.
    apply rmks'__fold_left in hi.
    destruct hi as [ys [e hi]].
    exists ys.
    apply PMF.elements_in_iff.
    exists e.
    apply In_InA; auto.
    apply grammar_eq_key_elt_equivalence.
  Qed.
 
  (* Soundness of the result of mk_rhs_map w.r.t. the input grammar *)

  (** Auxiliary invariant: every RHS stored in [rm] corresponds to a production in [prs]. *)
  Definition rms' (rm : rhs_map) (prs : list (production * grammar_entry)) : Prop :=
    forall x ys yss,
      NM.MapsTo x yss rm -> In ys yss -> exists e, In ((x, ys), e) prs.

  (** The empty [rhs_map] trivially satisfies [rms']. *)
  Lemma rms'_empty :
      rms' (NM.empty (list (list symbol))) [].
  Proof.
    intros x ys yss hm hi.
    exfalso.
    eapply NMF.empty_mapsto_iff; eauto.
  Qed.

  (** [add_production] preserves the [rms'] invariant when extending the production list. *)
  Lemma add_production_preserves_rms' :
    forall rm pr prs,
      rms' rm prs
      -> rms' (add_production (fst pr) (snd pr) rm) (prs ++ [pr]).
  Proof.
    intros rm ((x', ys'), e) prs hr x ys yss hm hi; sis. 
    destruct (NM.find _ _) as [yss' |] eqn:hf.
    - destruct (nt_eq_dec x' x) as [? | hneq]; subst.
      + apply NMF.add_mapsto_iff in hm.
        destruct hm as [[_ heq] | [? ?]]; tc; subst.
        destruct hi as [hh | ht]; subst.
        * exists e.
          apply in_or_app; right.
          apply in_eq.
        * apply NMF.find_mapsto_iff in hf.
          eapply hr in ht; eauto.
          destruct ht as [e' hi].
          exists e'.
          apply in_or_app; left; auto.
      + apply NM.add_3 in hm; auto.
        eapply hr in hi; eauto.
        destruct hi as [e' hi].
        exists e'.
        apply in_or_app; left; auto.
    - destruct (nt_eq_dec x' x) as [? | hneq]; subst.
      + apply NMF.add_mapsto_iff in hm.
        destruct hm as [[_ heq] | [? ?]]; tc; subst.
        apply in_singleton_eq in hi; subst.
        exists e.
        apply in_or_app; right.
        apply in_eq.
      + apply NM.add_3 in hm; auto.
        eapply hr in hi; eauto.
        destruct hi as [e' hi].
        exists e'.
        apply in_or_app; left; auto.
  Qed.

  (** Folding [add_production] over [prs] from the empty map satisfies [rms']. *)
    Lemma rms'__fold_left :
    forall (prs : list (production * grammar_entry)),
      rms'
        (fold_left (fun a p => add_production (fst p) (snd p) a)
                   prs
                   (NM.empty (list (list symbol))))
        prs.
  Proof.
    intros prs.
    apply fold_left_preserves_list_invar.
    - apply rms'_empty.
    - apply add_production_preserves_rms'.
  Qed.
  
  (** Soundness: every RHS in the [rhs_map] corresponds to a real production in [g]. *)
  Definition rhs_map_sound (rm : rhs_map) (g : grammar) :=
    forall x ys yss,
      NM.MapsTo x yss rm -> In ys yss -> PM.In (x, ys) g.

  (** [mk_rhs_map] satisfies [rhs_map_sound] for any grammar. *)
  Lemma mk_rhs_map_sound :
    forall g,
      rhs_map_sound (mk_rhs_map g) g.
  Proof.
    intros g x ys yss hm hi.
    unfold mk_rhs_map in hm.
    rewrite PM.fold_1 in hm.
    eapply rms'__fold_left in hi; eauto.
    destruct hi as [e hi].
    apply PMF.elements_in_iff.
    exists e.
    apply In_InA; auto.
    apply grammar_eq_key_elt_equivalence.
  Qed.

  (* Completeness of the result of mk_rhs_map w.r.t. the input grammar *)

  (** Auxiliary invariant: every production in [prs] has its RHS recorded in [rm]. *)
  Definition rmc' (rm : rhs_map) (prs : list (production * grammar_entry)) : Prop :=
    forall x ys e,
      In ((x, ys), e) prs
      -> exists yss, NM.MapsTo x yss rm /\ In ys yss.

  (** The empty [rhs_map] trivially satisfies [rmc']. *)
  Lemma rmc'_empty :
      rmc' (NM.empty (list (list symbol))) [].
  Proof.
    intros x ys e hi.
    inv hi. 
  Qed.

  (** [add_production] preserves the [rmc'] invariant when extending the production list. *)
  Lemma add_production_preserves_rmc' :
    forall rm pr prs,
      rmc' rm prs
      -> rmc' (add_production (fst pr) (snd pr) rm) (prs ++ [pr]).
  Proof.
    intros rm ((x', ys'), e') prs hr x ys e hi; sis.
    apply in_app_or in hi; destruct hi as [hl | hr'].
    - destruct (NM.find _ _) as [yss' |] eqn:hf.
      + destruct (nt_eq_dec x' x) as [? | hneq]; subst;
          apply hr in hl; destruct hl as [yss [hm hi]].
        * exists (ys' :: yss'); split; auto.
          -- apply NMF.add_mapsto_iff; auto.
          -- apply NMF.find_mapsto_iff in hm.
             rewrite hm in hf; inv hf; apply in_cons; auto.
        * exists yss; split; auto.
          apply NMF.add_mapsto_iff; auto.
      + destruct (nt_eq_dec x' x) as [? | hneq]; subst;
          apply hr in hl; destruct hl as [yss [hm hi]].
        * exists [ys']; split; auto.
          -- apply NMF.add_mapsto_iff; auto.
          -- apply NMF.find_mapsto_iff in hm.
             rewrite hm in hf; inv hf; apply in_cons; auto.
        * exists yss; split; auto.
          apply NM.add_2; auto.
    - apply in_singleton_eq in hr'; inv hr'.
      destruct (NM.find _ _) as [yss' |] eqn:hf; eexists; split;
        try (apply NMF.add_mapsto_iff; auto); try apply in_eq.
  Qed.
  
  (** Folding [add_production] over [prs] from the empty map satisfies [rmc']. *)
  Lemma rmc'__fold_left :
    forall (prs : list (production * grammar_entry)),
      rmc'
        (fold_left (fun a p => add_production (fst p) (snd p) a)
                   prs
                   (NM.empty (list (list symbol))))
        prs.
  Proof.
    intros prs.
    apply fold_left_preserves_list_invar.
    - apply rmc'_empty.
    - apply add_production_preserves_rmc'.
  Qed.

  (** Completeness: every production in [g] has its RHS recorded in the [rhs_map]. *)
  Definition rhs_map_complete (rm : rhs_map) (g : grammar) :=
    forall x ys,
      PM.In (x, ys) g -> exists yss, NM.MapsTo x yss rm /\ In ys yss.

  (** [mk_rhs_map] satisfies [rhs_map_complete] for any grammar. *)
  Lemma mk_rhs_map_complete :
    forall g,
      rhs_map_complete (mk_rhs_map g) g.
  Proof.
    intros g x ys hi.
    apply PMF.elements_in_iff in hi.
    destruct hi as [e hi].
    apply pm_in_a__in in hi.
    eapply rmc'__fold_left in hi.
    destruct hi as [yss [hm hi]].
    exists yss; split; auto.
    unfold mk_rhs_map.
    rewrite PM.fold_1; auto.
  Qed.

  (* Correctness spec for mk_rhs_map *)
  (** An [rhs_map] is correct for [g] if it is key-sound, value-sound, and complete. *)
  Definition rhs_map_correct (rm : rhs_map) (g : grammar) :=
    rhs_map_keys_sound rm g
    /\ rhs_map_sound rm g
    /\ rhs_map_complete rm g.

  (** A production in [g] has its RHS findable in a correct [rhs_map]. *)
  Lemma in_grammar_find_some :
    forall g rm x ys,
      rhs_map_correct rm g
      -> PM.In (x, ys) g
      -> exists yss,
          NM.find x rm = Some yss
          /\ In ys yss.
  Proof.
    intros g rm x ys [hs [hs' hc]] hi.
    apply hc in hi; destruct hi as [yss [hm hi]].
    apply NMF.find_mapsto_iff in hm; eauto.
  Qed.
  
  (** [mk_rhs_map] satisfies the full correctness specification for any grammar. *)
  Lemma mk_rhs_map_correct :
    forall (g : grammar),
      rhs_map_correct (mk_rhs_map g) g.
  Proof.
    intros g; repeat split.
    - apply mk_rhs_map_keys_sound.
    - apply mk_rhs_map_sound.
    - apply mk_rhs_map_complete.
  Qed.

  (** The list of nonterminal keys present in an [rhs_map]. *)
  Definition keys (rm : rhs_map) : list nonterminal :=
    fold_right (fun pr l => fst pr :: l) [] (NM.elements rm).

  (** The LHS of any grammar production is in the [keys] of a correct [rhs_map]. *)
  Lemma production_lhs_in_keys :
    forall g rm x ys,
      rhs_map_correct rm g
      -> PM.In (x, ys) g
      -> In x (keys rm).
  Proof.
    intros g rm x ys hc hi.
    apply in_map_iff.
    destruct hc as [_ [_ hc]].
    apply hc in hi.
    destruct hi as [yss [hm hi]].
    exists (x, yss); split; auto.
    apply nm_mapsto_elements_iff; auto.
  Qed.
    
  (** The set of nonterminal keys present in an [rhs_map], as a finite set. *)
  Definition key_set (rm : rhs_map) : NtSet.t :=
    from_nt_list (keys rm).

  (** The LHS of any grammar production is in the [key_set] of a correct [rhs_map]. *)
  Lemma production_lhs_in_key_set :
    forall g rm x ys,
      rhs_map_correct rm g
      -> PM.In (x, ys) g
      -> NtSet.In x (key_set rm).
  Proof.
    intros.
    eapply from_nt_list_in_iff.
    eapply production_lhs_in_keys; eauto.
  Qed.
  
  (** Looks up all right-hand sides for nonterminal [x] in an [rhs_map]; returns [] if absent. *)
  Definition rhss_for (x : nonterminal) (rm : rhs_map) : list (list symbol) :=
    match NM.find x rm with
    | Some yss => yss
    | None     => []
    end.
  
  (** [rhss_for] membership and grammar membership coincide for a correct [rhs_map]. *)
  Lemma rhss_for_in_iff :
    forall g rm x ys,
      rhs_map_correct rm g
      -> In ys (rhss_for x rm) <-> PM.In (x, ys) g.
  Proof.
    unfold rhss_for; intros g rm x ys [hs [hs' hc]]; split; intros hi.
    - destruct (NM.find _ _) eqn:hf; try inv hi.
      apply NMF.find_mapsto_iff in hf; eauto.
    - apply hc in hi; destruct hi as [yss [hm hi]].
      destruct (NM.find _ _) as [yss' |] eqn:hf;
        apply NMF.find_mapsto_iff in hm;
        rewrite hm in hf; inv hf; auto.
  Qed.

  (** If [ys] is in [rhss_for x rm] then [x] is in [keys rm]. *)
  Lemma rhss_for_keys :
    forall x ys rm,
      In ys (rhss_for x rm) -> In x (keys rm).
  Proof.
    intros x ys rm hi; unfold rhss_for in hi.
    destruct (NM.find _ _) as [yss |] eqn:hf; try solve [inv hi].
    apply NMF.find_mapsto_iff in hf.
    apply NMF.elements_mapsto_iff in hf.
    apply InA_alt in hf.
    destruct hf as [(x', yss') [heq hi']]; inv heq; sis; subst.
    apply in_map_iff. 
    exists (x', yss'); split; auto.
  Qed.
  
  (** If [ys] is in [rhss_for x rm] then [x] is in [key_set rm]. *)
  Lemma rhss_for_key_set :
    forall x ys rm,
      In ys (rhss_for x rm) -> NtSet.In x (key_set rm).
  Proof.
    intros.
    apply from_nt_list_in_iff.
    eapply rhss_for_keys; eauto.
  Qed.

  (** [rhss_for x rm] membership witnesses a containing list in the map's element list. *)
  Lemma rhss_for_elements :
    forall x ys rm,
      In ys (rhss_for x rm)
      -> (exists yss, In (x, yss) (NM.elements rm) /\ In ys yss).
  Proof.
    intros x ys rm hi.
    unfold rhss_for in hi.
    destruct (NM.find _ _) as [yss |] eqn:hf.
    - exists yss; split; auto.
      apply NMF.find_mapsto_iff in hf.
      apply nm_mapsto_elements_iff; auto.
    - inv hi.
  Qed.

  (** If [y] is in the value list at key [x] in [prs], then [y] is in the flat concatenation of all values. *)
  Lemma rhss_for_all_rhss' :
    forall A B (x : A) (y : B) ys prs,
      In (x, ys) prs
      -> In y ys
      -> In y (List.concat (List.map snd prs)).
  Proof.
    intros A B x y ys prs hi hi'.
    induction prs as [| (x', y') prs IH]; sis.
    - inv hi.
    - destruct hi as [hh | ht].
      + inv hh;
        apply in_or_app; auto.
      + apply in_or_app; auto.
  Qed.
  
  (** Any RHS reachable via [rhss_for] also appears in [all_rhss]. *)
  Lemma rhss_for_all_rhss :
    forall x ys rm,
      In ys (rhss_for x rm)
      -> In ys (all_rhss rm).
  Proof.
    intros x ys rm hi.
    apply rhss_for_elements in hi.
    destruct hi as [yss [hi hi']].
    eapply rhss_for_all_rhss'; eauto.
  Qed.

(*
  Lemma in_grammar__key_set :
    forall g pm x ys,
      production_map_correct pm g
      -> In (x, ys) g
      -> NtSet.In x (key_set pm).
  Proof.
    intros g pm x ys hp hi.
    eapply rhss_for_key_set.
    eapply rhss_for_in_iff; eauto.
  Qed.
  
  Definition rhs_lengths (g : grammar) : list nat :=
    map (fun rhs => List.length rhs) (rhss g).
 *)
  
  (* The next two definitions help us use a well-founded measure that is 
     already defined in terms of a grammar, rather than a production map *)

  (*
  Definition decompress (e : nonterminal * list (list symbol)) : list production :=
    match e with
    | (x, yss) => map (pair x) yss
    end.

  Lemma decompress_nt_eq :
    forall x x' ys yss,
      In (x, ys) (decompress (x', yss))
      -> x' = x.
  Proof.
    intros x x' ys yss hi; sis.
    apply in_map_iff in hi; destruct hi as [? [heq hi]].
    inv heq; auto.
  Qed.

  Definition grammar_of (pm : production_map) : grammar :=
    flat_map decompress (NM.elements pm).

  Lemma rhss_for_grammar_of :
    forall x ys pm,
      In ys (rhss_for x pm) -> In (x, ys) (grammar_of pm).
  Proof.
    unfold rhss_for, grammar_of; intros x ys pm hi.
    destruct (NM.find _ _) as [yss |] eqn:hf; try solve [inv hi].
    apply in_flat_map.
    exists (x, yss); split.
    - apply NMF.find_mapsto_iff in hf.
      apply NMF.elements_mapsto_iff in hf.
      apply InA_alt in hf.
      destruct hf as [(x', yss') [heq hi']].
      repeat red in heq; sis; destruct heq; subst; auto.
    - apply in_map_iff; eauto.
  Qed.

  Lemma in_elements__in_fold_right_add_key :
    forall (x   : nonterminal)
           (yss : list (list symbol))
           (prs : list (nonterminal * list (list symbol))),
      In (x, yss) prs
      -> In x (fold_right (fun pr l => fst pr :: l) [] prs).
    intros x yss prs hi; induction prs as [| (x', yss') prs Ih]; sis; auto.
    destruct hi as [hh | ht]; auto.
    inv hh; auto.
  Qed.
  
  Lemma grammar_of_key_set :
    forall x ys pm,
      In (x, ys) (grammar_of pm)
      -> NtSet.In x (key_set pm).
  Proof.
    intros x ys pm hi.
    apply in_flat_map in hi; destruct hi as [(x', yss) [hi hi']].
    apply decompress_nt_eq in hi'; subst.
    apply from_nt_list_in_iff.
    eapply in_elements__in_fold_right_add_key; eauto.
  Qed.

  Lemma in_grammar__in_grammar_of :
    forall g pm x ys,
      production_map_correct pm g
      -> In (x, ys) g
      -> In (x, ys) (grammar_of pm).
  Proof.
    intros g pm x ys hc hi.
    apply rhss_for_grammar_of.
    eapply rhss_for_in_iff; eauto.
  Qed.
  
  Lemma rhss_rhs_lengths_in :
    forall g rhs,
      In rhs (rhss g)
      -> In (List.length rhs) (rhs_lengths g).
  Proof.
    intros g rhs hin; induction g as [| (x, rhs') ps Ih];
      simpl in *; inv hin; auto.
  Qed.

  Definition max_rhs_length (g : grammar) : nat :=
    list_max (rhs_lengths g).

  Lemma grammar_rhs_length_le_max :
    forall g x rhs,
      In (x, rhs) g
      -> List.length rhs <= max_rhs_length g.
  Proof.
    intros; unfold max_rhs_length.
    apply list_max_in_le.
    apply rhss_rhs_lengths_in.
    eapply rhssForNt_rhss.
    eapply rhssForNt_in_iff; eauto.
  Qed.

  Lemma grammar_rhs_length_lt_max_plus_1 :
    forall g x rhs,
      In (x, rhs) g
      -> List.length rhs < 1 + max_rhs_length g.
  Proof.
    intros g x rhs hin.
    apply grammar_rhs_length_le_max in hin; omega.
  Qed.

  Definition all_nts (g : grammar) : NtSet.t := 
    from_nt_list (lhss g).

  Lemma all_nts_lhss_iff :
    forall (g : grammar) (x : nonterminal),
      In x (lhss g)
      <-> NtSet.In x (all_nts g).
  Proof.
    intros g x; split; intros hi; apply from_nt_list_in_iff; auto.
  Qed.

  Lemma lhs_mem_all_nts_true :
    forall g x ys,
      In (x, ys) g
      -> NtSet.mem x (all_nts g) = true.
  Proof.
    intros g x ys hi.
    apply NF.mem_iff.
    apply all_nts_lhss_iff. 
    eapply production_lhs_in_lhss; eauto.
  Qed.
   *)
  
  (* Definitions related to input that the parser consumes. *)
  (** A token is a terminal symbol tagged with its semantic value. *)
  Definition token   := {a : terminal & t_semty a}.

  (** Displays a token as a parenthesized terminal name for error messages. *)
  Definition show_token (t : token) : string :=
    match t with
    | @existT _ _ a _ => "(" ++ showT a ++ ")"
    end.

  (* Concrete syntax trees *)
  (** A concrete syntax tree: either a [leaf] terminal or a [node] nonterminal with children. *)
  Inductive tree    := leaf : terminal -> tree
                     | node : nonterminal -> list tree -> tree.

  (** A forest is a list of concrete syntax trees. *)
  Definition forest := list tree.

  (* The next two functions are used to validate
     the output of extracted parsers *)
  (** Counts the number of nodes (both leaves and non-leaves) in a tree. *)
  Fixpoint count_nodes (t : tree) : nat :=
    match t with
    | leaf _     => 1
    | node _ sts =>
      let fix count_nodes' (f : forest) : nat :=
          match f with
          | []      => 0
          | t :: f' => count_nodes t + count_nodes' f'
          end
      in  count_nodes' sts
    end.

  (** Extracts the sequence of terminals (yield) from a concrete syntax tree. *)
  Fixpoint flatten (t : tree) : list terminal :=
    match t with
    | leaf t     => [t]
    | node _ sts => flat_map flatten sts
    end.

  (* Parser stacks *)

  (* The stack used in LL prediction and parsing *)

  (** A parser frame: [pre] is the already-matched prefix (reversed), [sem] holds its semantic values,
      and [suf] is the remaining suffix of the production RHS to be matched. *)
  Inductive parser_frame : Type :=
  | Fr (pre : list symbol)       (* rhs prefix *)
       (sem : symbols_semty pre) (* sem value for prefix *)
       (suf : list symbol).      (* rhs suffix *)

  (** Equal parser frames with the same [pre] have equal semantic values. *)
  Lemma frames_eq__semvals_eq :
    forall pre vs vs' suf suf',
      Fr pre vs suf = Fr pre vs' suf'
      -> vs = vs'.
  Proof.
    intros pre vs vs' suf suf' heq.
    inv heq.
    ss_inj; auto.
  Qed.
  
  (** Extracts the remaining suffix of symbols from a parser frame. *)
  Definition suffix (fr : parser_frame) : list symbol :=
    match fr with
    | Fr _ _ suf => suf
    end.

  (** A parser stack: a non-empty stack of parser frames represented as a head-frame and a list of tail frames. *)
  Definition parser_stack : Type :=
    (parser_frame * list parser_frame)%type.

  (** Collects the unprocessed symbols contributed by each tail frame to the overall suffix. *)
  Fixpoint unproc_tail_syms (frs : list parser_frame) : list symbol :=
    match frs with 
    | []                           => []
    | Fr _ _ [] :: _               => [] (* impossible for a well-formed stack *)
    | Fr _ _ (T _ :: _) :: _       => [] (* impossible for a well-formed stack *)
    | Fr _ _ (NT x :: suf) :: frs' => suf ++ unproc_tail_syms frs'
    end.

  (** All unprocessed symbols in the entire parser stack, head frame first. *)
  Definition unproc_stack_syms (stk : parser_stack) : list symbol :=
    match stk with
    | (Fr _ _ suf, frs) => suf ++ unproc_tail_syms frs
    end.

  (** Projects the suffix of the head frame and the suffixes of all tail frames from a parser stack. *)
  Definition stack_suffixes (stk : parser_stack) : list symbol * list (list symbol) :=
    match stk with
    | (fr, frs) => (suffix fr, map suffix frs)
    end.

  (** The full RHS (prefix reversed and appended to suffix) of the bottom frame of a parser stack. *)
  Definition bottom_frame_syms (stk : parser_stack) : list symbol :=
    match bottom_elt stk with
    | Fr pre _ suf => rev pre ++ suf
    end.

  (** An LL subparser: a predicted RHS [prediction] paired with the current parser stack [stack]. *)
  Record subparser := Sp { prediction : list symbol
                           ; stack      : parser_stack }.

  (** Equal subparsers have equal head frames. *)
  Lemma sps_eq__head_frames_eq :
    forall pred pred' fr fr' frs frs',
      Sp pred (fr, frs) = Sp pred' (fr', frs')
      -> fr = fr'.
  Proof.
    intros pred pred' fr fr' frs frs' heq; inv heq; auto.
  Qed.

  (** Inversion lemma: equal subparsers with a terminal-headed prefix give equal components up to cast. *)
  Lemma inv_sp_eq_terminal_head :
    forall pred a pre v vs suf frs pred' pre' vs' suf' frs',
      Sp pred (Fr (T a :: pre) (v, vs) suf, frs) = Sp pred' (Fr pre' vs' suf', frs')
      -> pred = pred'
         /\ suf = suf'
         /\ frs = frs'
         /\ exists (heq : T a :: pre = pre'),
             (cast_ss _ _ heq (v, vs)) = vs'.
  Proof.
    intros pred a pre v vs suf frs pred' pre' vs' suf' frs' heq.
    pose proof heq as heq'.
    inv heq.
    apply sps_eq__head_frames_eq in heq'.
    apply frames_eq__semvals_eq in heq'; subst.
    repeat split; auto.
    exists eq_refl.
    rewrite cast_ss_refl; auto.
  Qed.

  (* The stack used in SLL prediction *)

  (** An SLL frame: an optional caller nonterminal context and the remaining suffix to match. *)
  Inductive sll_frame :=
  | sll_fr : option nonterminal -> list symbol -> sll_frame.

  (** Extracts the suffix component from an SLL frame. *)
  Definition sll_suffix (fr : sll_frame) : list symbol :=
    match fr with
    | sll_fr _ suf => suf
    end.

  (** Packages [sll_frame] with a lexicographic order for use in ordered sets and maps. *)
  Module SllFrAsUOT <: UsualOrderedType.

    Module O  := OptionAsUOT NTAsUOT.
    Module L  := ListAsUOT SymbolAsUOT.
    Module P  := PairAsUOT O L.

    Definition t := sll_frame.

    Definition eq       := @eq t.
    Definition eq_refl  := @eq_refl t.
    Definition eq_sym   := @eq_sym t.
    Definition eq_trans := @eq_trans t.

    (** Lexicographic order on SLL frames, delegating to the pair order on (option NT, suffix). *)
    Definition lt x y :=
      match x, y with
      | sll_fr o suf, sll_fr o' suf' =>
        P.lt (o, suf) (o', suf')
      end.

    (** Transitivity of the SLL frame order. *)
    Lemma lt_trans :
      forall x y z,
        lt x y -> lt y z -> lt x z.
    Proof.
      unfold lt; intros [o suf] [o' suf'] [o'' suf'']; eapply P.lt_trans; eauto.
    Qed.

    (** Irreflexivity of the SLL frame order. *)
    Lemma lt_not_eq :
      forall x y, lt x y -> ~ x = y.
    Proof.
      unfold lt; intros [o suf] [o' suf'] hl he; inv he.
      eapply P.lt_not_eq; eauto.
    Qed.

    (** Three-way comparison for SLL frames, compatible with [lt] and [eq]. *)
    Definition compare (x y : sll_frame) : Compare lt eq x y.
      refine (match x, y with
              | sll_fr o suf, sll_fr o' suf' =>
                match P.compare (o, suf) (o', suf') with
                | LT hl => LT _
                | GT he => GT _
                | EQ hl => EQ _
                end
              end); red; tc.
    Defined.
      
    (** Decidable equality for SLL frames. *)
    Definition eq_dec (x y : sll_frame) : {x = y} + {x <> y}.
      refine (match x, y with
              | sll_fr o suf, sll_fr o' suf' =>
                match P.eq_dec (o, suf) (o', suf') with
                | left he  => left _
                | right hn => right _
                end
              end); tc.
    Defined.

  End SllFrAsUOT.

  (* Finite sets of SLL frames *)
  Module FS  := FSetAVL.Make SllFrAsUOT.
  Module FSF := FSetFacts.Facts FS.
  Crane NoArena FS.MSet.Raw.tree.

  (* Finite maps with SLL frame keys *)
  Module FM  := FMapAVL.Make SllFrAsUOT.
  Module FMF := FMapFacts.Facts FM.
  Crane NoArena FM.Raw.tree.

  (* Module for finding the transitive closure
     of a finite graph with SLL frame nodes *)
  Module TC  := TransClos.Make FS FM.

  (** An SLL stack: a non-empty stack of SLL frames, used during Strong LL prediction. *)
  Definition sll_stack := (sll_frame * list sll_frame)%type.
  
  (** Projects the suffix of the head SLL frame and all tail-frame suffixes from an SLL stack. *)
  Definition sll_stack_suffixes (stk : sll_stack) : list symbol * list (list symbol) :=
    match stk with
    | (fr, frs) => (sll_suffix fr, map sll_suffix frs)
    end.

  (** An SLL subparser: a predicted RHS [sll_pred] together with an SLL stack [sll_stk]. *)
  Record sll_subparser : Type :=
    sll_sp { sll_pred : list symbol;
            sll_stk  : sll_stack }.

  (* Projecting an SLL subparser from an LL subparser *)


  (*Definition sllify' (fr : parser_frame) : suffix_frame :=
    match fr with
    | Fr _ _ suf => SF None suf
    end.

  Definition sllify (stk : parser_stack) : suffix_stack :=
    match stk with
    | (fr, frs) => (sllify' fr, map sllify' frs)
    end.

  Definition sllify_sp (sp : subparser) : sll_subparser :=
    match sp with
    | Sp pred stk => sll_sp pred (sllify stk)
    end. *)

  (* Grammatical derivation relations -- the main parser correctnes spec *)

  (* Derivation relation for concrete syntax trees *)
  (** [tree_derivation g s w t] holds when token list [w] is derived from symbol [s] via tree [t] in [g]. *)
  Inductive tree_derivation (g : grammar) : symbol -> list token -> tree -> Prop :=
  | leaf_der  : 
      forall (a : terminal) (v : t_semty a),
        tree_derivation g (T a) [@existT _ _ a v] (leaf a)
  | node_der : 
      forall (x  : nonterminal) (ys : list symbol) (w : list token) (sts : forest),
        PM.In (x, ys) g
        -> forest_derivation g ys w sts
        -> tree_derivation g (NT x) w (node x sts)
  with forest_derivation (g : grammar) : list symbol -> list token-> forest-> Prop :=
       | nil_forest_der  : 
           forest_derivation g [] [] []
       | cons_forest_der : 
           forall (s : symbol) (ss : list symbol) (wpre wsuf : list token) 
                  (tr : tree) (trs : list tree),
             tree_derivation g s wpre tr
             -> forest_derivation g ss wsuf trs
             -> forest_derivation g (s :: ss) (wpre ++ wsuf) (tr :: trs).

  Hint Constructors tree_derivation forest_derivation : core.

  Scheme tree_derivation_mutual_ind   := Induction for tree_derivation Sort Prop
    with forest_derivation_mutual_ind := Induction for forest_derivation Sort Prop.

  Ltac inv_td hs  hi hg:=
    inversion hs as [ ? ? | ? ? ? ? hi hg]; subst; clear hs.

  Ltac inv_fd hg  hs hg' :=
    inversion hg as [| ? ? ? ? ? ? hs hg']; subst; clear hg.

  (** [forest_derivation] is closed under list concatenation of symbol lists, token lists, and forests. *)
  Lemma forest_derivation_app' :
    forall g ys1 w1 v1,
      forest_derivation g ys1 w1 v1
      -> forall ys2 w2 v2,
        forest_derivation g ys2 w2 v2
        -> forest_derivation g (ys1 ++ ys2) (w1 ++ w2) (v1 ++ v2).
  Proof.
    intros g ys1 w1 v1 hg.
    induction hg; intros ys2 w2 v2 hg2; simpl in *; auto.
    rewrite <- app_assoc; constructor; auto.
  Qed.

  (** Convenience wrapper for [forest_derivation_app']: appends two forest derivations. *)
  Lemma forest_derivation_app :
    forall g ys ys' w w' v v',
      forest_derivation g ys w v
      -> forest_derivation g ys' w' v'
      -> forest_derivation g (ys ++ ys') (w ++ w') (v ++ v').
  Proof.
    intros; eapply forest_derivation_app'; eauto.
  Qed.

  (** Appends a forest derivation with a single nonterminal node derivation at the end. *)
  Lemma forest_app_singleton_node :
    forall g x ys ys' w w' v v',
      PM.In (x, ys') g
      -> forest_derivation g ys w v
      -> forest_derivation g ys' w' v'
      -> forest_derivation g (ys ++ [NT x]) (w ++ w') (v ++ [node x v']).
  Proof.
    intros g x ys ys' w w' v v' hi hg hg'.
    apply forest_derivation_app; auto.
    rew_nil_r w'; eauto.
  Qed.

  (** Prepends a single terminal leaf to a forest derivation. *)
  Lemma terminal_head_forest_derivation :
    forall g a v ys w ts,
      forest_derivation g ys w ts
      -> forest_derivation g (T a :: ys) ((@existT _ _ a v) :: w) (leaf a :: ts).
  Proof.
    intros g a v ys w ts hg.
    assert (happ : (@existT _ _  a v) :: w =
                   [@existT _ _ a v] ++ w)
      by apply cons_app_singleton.
    rewrite happ; auto.
  Qed.

  (** Splits a forest derivation over a concatenated symbol list into two forest derivations. *)
  Lemma forest_derivation_split :
    forall g ys ys' w'' v'',
      forest_derivation g (ys ++ ys') w'' v''
      -> exists w w' v v',
        w'' = w ++ w'
        /\ v'' = v ++ v'
        /\ forest_derivation g ys  w  v
        /\ forest_derivation g ys' w' v'.
  Proof.
    intros g ys; induction ys as [| y ys Ih]; intros ys' w'' v'' hg; sis.
    - exists []; exists w''; exists []; exists v''; repeat split; auto.
    - inversion hg as [| s ss wpre wsuf t f hs hg']; subst; clear hg. 
      apply Ih in hg'; destruct hg' as [w [w' [v [v' [? [? [hg' hg'']]]]]]]; subst.
      exists (wpre ++ w); exists w'; exists (t :: v); exists v'. 
      repeat split; auto; apps.
  Qed.

  (** Peels off the final terminal derivation from a forest derivation ending in [T a]. *)
  Lemma forest_derivation_terminal_end :
    forall g ys a w v,
      forest_derivation g (ys ++ [T a]) w v
      -> exists w_front l v_front,
        w = w_front ++ [@existT _ _ a l]
        /\ v = v_front ++ [leaf a]
        /\ forest_derivation g ys w_front v_front.
  Proof.
    intros g ys a w v hg.
    eapply forest_derivation_split in hg.
    destruct hg as [w' [w'' [v' [v'' [? [? [hg hg']]]]]]]; subst.
    inv_fd hg' ht hg''.
    inv_td ht hi hf.
    inv_fd hg'' ht hg'''.
    repeat eexists; eauto.
  Qed.

  (** Peels off the final nonterminal derivation from a forest derivation ending in [NT x]. *)
  Lemma forest_derivation_nonterminal_end :
    forall g ys x w v,
      forest_derivation g (ys ++ [NT x]) w v
      -> exists wpre wsuf vpre v',
        w = wpre ++ wsuf
        /\ v = vpre ++ [node x v']
        /\ forest_derivation g ys wpre vpre
        /\ tree_derivation g (NT x) wsuf (node x v').
  Proof.
    intros g ys x w v hg.
    eapply forest_derivation_split in hg.
    destruct hg as [w' [w'' [v' [v'' [? [? [hg hg']]]]]]]; subst.
    inv_fd hg' ht hg''.
    inv_td ht hi hf.
    inv_fd hg'' ht hg'''.
    rewrite app_nil_r.
    repeat eexists; eauto.
  Qed.

  (** Inversion on a leaf tree derivation: the symbol must be [T a] and the word a singleton token. *)
  Lemma inv_leaf_treeder :
    forall g s w a,
      tree_derivation g s w (leaf a)
      -> s = T a  /\ exists v, w = [@existT _ _ a v].
  Proof.
    intros g s w a hd; inv hd; eauto.
  Qed.

  (** Inversion on a node tree derivation: the symbol must be [NT x] with a grammar production. *)
  Lemma inv_node_treeder :
    forall g s w x sts,
      tree_derivation g s w (node x sts)
      -> s = NT x /\ exists ys, PM.In (x, ys) g /\ forest_derivation g ys w sts.
  Proof.
    intros g s w x sts hd; inv hd; eauto.
  Qed.

  (** Inversion on a cons forest derivation: decomposes the head tree and tail forest. *)
  Lemma inv_cons_forestder :
    forall g ss w t ts,
      forest_derivation g ss w (t :: ts)
      -> exists s ss' w1 w2,
        ss = s :: ss'
        /\ w = w1 ++ w2
        /\ tree_derivation g s w1 t
        /\ forest_derivation g ss' w2 ts.
  Proof.
    intros g ss w t ts hd; inv hd; eauto 8.
  Qed.
            
  (** Strips semantic values from a token list, returning just the terminal symbols. *)
  Definition terminals (ts : list token) : list terminal :=
    map (@projT1 _ t_semty) ts.

  (** [terminals] distributes over list append. *)
  Lemma terminals_app :
    forall ts ts',
      terminals (ts ++ ts') = terminals ts ++ terminals ts'.
  Proof.
    intros ts ts'.
    unfold terminals.
    apply map_app.
  Qed.

  (** If two derivations produce the same forest and their words+suffixes are equal, the words and symbol lists are equal. *)
  Lemma forests_eq__words_eq_rhss_eq' :
    forall g ys w ts,
      forest_derivation g ys w ts
      -> forall w' suf suf' ys',
        forest_derivation g ys' w' ts
        -> w ++ suf = w' ++ suf'
        -> w' = w /\ suf' = suf /\ ys' = ys.
  Proof.
    intros g ys w ts hf. 
    induction hf using forest_derivation_mutual_ind with
        (P := fun s w t (hs : tree_derivation g s w t) =>
                forall w' suf suf' s',
                  tree_derivation g s' w' t
                  -> w ++ suf = w' ++ suf'
                  -> w' = w /\ suf' = suf /\ s' = s).
    - intros w' suf suf' s' hd heq; sis.
      apply inv_leaf_treeder in hd.
      destruct hd as [? [v' heq']]; subst.
      inv heq; repeat split; auto.
      apply heads_eq_tails_eq__lists_eq; auto.
    - intros w' suf suf' s' hd heq.
      apply inv_node_treeder in hd.
      destruct hd as [? [ys' [hi hd]]]; subst.
      eapply IHhf in hd; eauto.
      firstorder.
    - intros w' suf suf' ys' hd heq; inv hd; auto.
    - intros w' suf suf' ys' hd heq.
      apply inv_cons_forestder in hd.
      destruct hd as [s' [ss' [w1 [w2 [heq' [heq'' [hd hd']]]]]]]; subst.
      repeat rewrite <- app_assoc in heq.
      eapply IHhf in hd; eauto.
      destruct hd as [? [heq' ?]]; subst.
      eapply IHhf0 in hd'; eauto.
      destruct hd' as [? [? ?]]; subst; auto.
  Qed.

  (** If two derivations produce the same forest and have a common suffix extension, the prefixes and symbol lists match. *)
  Lemma forests_eq__words_eq_rhss_eq :
    forall g ys ys' pre pre' suf suf' ts,
      forest_derivation g ys pre ts
      -> forest_derivation g ys' pre' ts
      -> pre ++ suf = pre' ++ suf'
      -> pre' = pre /\ suf' = suf /\ ys' = ys.
  Proof.
    intros. eapply forests_eq__words_eq_rhss_eq'; eauto.
  Qed.
  
(*  Lemma forests_eq__rhss_eq' :
    forall g ys w ts,
      forest_derivation g ys w ts
      -> forall w' ys',
        forest_derivation g ys' w' ts
        -> (terminals w' = terminals w) /\ ys' = ys.
  Proof.
    intros g ys w ts hf. 
    induction hf using forest_derivation_mutual_ind with
        (P := fun s w t (hs : tree_derivation g s w t) =>
                forall w' s',
                  tree_derivation g s' w' t
                  -> terminals w' = terminals w /\ s' = s).
    - intros w' s' hs; inv hs; auto.
    - intros w' s' hs; inv hs; firstorder.
    - intros w' ys' hf; auto; inv hf; auto. 
    - intros w' ys' hf'.
      inv hf'.
      apply IHhf in H3.
      destruct H3 as [ht ?]; subst.
      apply IHhf0 in H4.
      destruct H4 as [ht' ?]; subst.
      split; auto.
      repeat rewrite terminals_app.
      rewrite ht.
      rewrite ht'; auto.
  Qed. *)

(*  Lemma forests_eq__rhss_eq :
    forall g ys ys' w ts,
      forest_derivation g ys w ts
      -> forest_derivation g ys' w ts
      -> ys' = ys.
  Proof.
    intros g ys ys' w ts hf hf'.
    eapply forests_eq__rhss_eq'
      with (ys := ys) (ys' := ys') in hf'; eauto.
    firstorder.
  Qed. *)

(*  Lemma trees_eq__forests_eq_words_eq' :
    forall g ys w v,
      forest_derivation g ys w v
      -> forall ys' w',
        forest_derivation g ys' w' v
        -> ys' = ys /\ w' = w.
  Proof.
    intros g ys w v hg.
    induction hg using forest_derivation_mutual_ind with
        (P := fun s w t (hs : tree_derivation g s w t) =>
                forall s' w',
                  tree_derivation g s' w' t
                  -> s' = s /\ w' = w).
    - intros s' w' hs; inv hs; auto.
    - intros s' w' hs; inv hs; firstorder.
    - intros ys' w' hg; inv hg; auto.
    - intros ys' w' hg'; inv hg'.
      apply Ihhg in h3; destruct h3; subst.
      apply Ihhg0 in h4; destruct h4; subst; auto.
  Qed. 

  Lemma trees_eq__gammas_eq_words_eq :
    forall g ys ys' w w' v,
      gamma_derivation g ys w v
      -> gamma_derivation g ys' w' v
      -> ys' = ys /\ w' = w.
  Proof.
    intros; eapply trees_eq__gammas_eq_words_eq'; eauto.
  Qed.

 *)

  (** A singleton terminal forest derivation yields a single-token word and a single leaf. *)
  Lemma forest_derivation_singleton_t :
    forall g a w v,
      forest_derivation g [T a] w v
      -> exists l,
        w = [@existT _ _ a l]
        /\ v = [leaf a].
  Proof.
    intros g a w v hg.
    inv_fd hg hs hg'.
    inv hs; inv hg'; rewrite app_nil_r; eauto.
  Qed.

  (** A singleton nonterminal forest derivation yields a single-node forest using some grammar production. *)
  Lemma forest_derivation_singleton_nt :
    forall g x w v,
      forest_derivation g [NT x] w v
      -> exists ys v',
        PM.In (x, ys) g
        /\ v = [node x v']
        /\ forest_derivation g ys w v'.
  Proof.
    intros g x w v hg.
    inv_fd hg hs hg'.
    inv hs; inv hg'; rewrite app_nil_r; eauto.
  Qed.

  (** Converts a singleton nonterminal forest derivation into a single tree derivation. *)
  Lemma forest_der_singleton__tree_der :
    forall gr x w ts,
      forest_derivation gr [NT x] w ts
      -> exists t, ts = [t] /\ tree_derivation gr (NT x) w t.
  Proof.
    intros gr x w ts hf.
    apply forest_derivation_singleton_nt in hf.
    destruct hf as (ys & ts' & hi & heq & hf); subst; eauto.
  Qed.

  (** A unique forest derivation: [v] is the only forest that [ss] derives from [w] in [g]. *)
  Definition unique_forest_derivation g ss w v :=
    forest_derivation g ss w v
    /\ forall v', forest_derivation g ss w v' -> v = v'.

  (* Derivation relation for semantic values *)
  (** [sem_value_derivation g s w v] holds when [w] derives semantic value [v] for symbol [s] via [g]'s actions. *)
  Inductive sem_value_derivation (g : grammar) :
    forall (s : symbol), list token -> symbol_semty s -> Prop :=
  | T_der  : 
      forall (a : terminal) (v : t_semty a),
        sem_value_derivation g (T a) [@existT _ _ a v] v
  | nt_der : 
      forall (x  : nonterminal)
             (ys : list symbol)
             (w  : list token)
             (vs : symbols_semty ys)
             (p  : predicate_semty (x, ys))
             (f  : action_semty (x, ys)),
        PM.MapsTo (x, ys) (@existT _ _ (x, ys) (p, f)) g
        -> sem_values_derivation g ys w vs
        -> p vs = true
        -> sem_value_derivation g (NT x) w (f vs)
  with sem_values_derivation (g : grammar) :
         forall (ys : list symbol), list token -> (symbols_semty ys) -> Prop :=
       | Nil_der  : 
           sem_values_derivation g [] [] tt
       | Cons_der : 
           forall (s     : symbol)
                  (ss    : list symbol)
                  (w1 w2 : list token) 
                  (v     : symbol_semty s)
                  (vs    : symbols_semty ss),
             sem_value_derivation g s w1 v
             -> sem_values_derivation g ss w2 vs
             -> sem_values_derivation g (s :: ss) (w1 ++ w2) (v, vs).

  Hint Constructors sem_value_derivation sem_values_derivation : core.

  Scheme sem_value_derivation_mutual_ind  := Induction for sem_value_derivation Sort Prop
    with sem_values_derivation_mutual_ind := Induction for sem_values_derivation Sort Prop.

  Ltac inv_sv hv  hm hvs hp :=
    inversion hv as [ ? ?
                    | ? ? ? ? ? ? hm hvs hp]; subst; clear hv.

  Ltac inv_svs hvs  hv hvs' :=
    inversion hvs as [| ? ? ? ? ? ? hv hvs']; subst; clear hvs.

  Ltac inv_t_der :=
    match goal with
    | H : sem_value_derivation _ (T _) _ _ |- _ =>
      inv H
    end.

  Ltac inv_nt_der :=
    match goal with
    | H : sem_value_derivation _ (NT _) _ _ |- _ =>
      inv H
    end.

  (** If a uniqueness property holds for all casts of [vs], then [vs] is the unique derivation for [ys, w]. *)
  Lemma foo :
    forall g (ys : list symbol) w vs,
      sem_values_derivation g ys w vs
      -> (forall ys' vs' (heq : ys = ys'),
             sem_values_derivation g ys' w vs'
             -> vs' = (cast_ss ys ys' heq vs))
      -> (forall vs',
             sem_values_derivation g ys w vs'
             -> vs' = vs).
  Proof.
    intros g ys w vs hd ha vs' hd'.
    apply ha with (heq := eq_refl) in hd'.
    unfold cast_ss in hd'.
    unfold eq_rect_r in hd'.
    rewrite <- Eqdep_dec.eq_rect_eq_dec in hd'; auto.
    apply GammaAsUOT.eq_dec.
  Qed.
  
  (** Inversion on a terminal semantic derivation: the word is exactly the singleton token [a, v]. *)
  Lemma inv_t_semder :
    forall g a w v,
      sem_value_derivation g (T a) w v
      -> w = [@existT _ _ a v].
  Proof.
    intros g a w v hs.
    inversion hs as [? ? h h' heq |]; subst; clear hs.
    apply Eqdep_dec.inj_pair2_eq_dec in heq; subst; auto.
    apply SymbolAsUOT.eq_dec.
  Qed.

  (** Inversion on a nonterminal semantic derivation: exposes the production, predicate, action, and sub-values. *)
  Lemma inv_nt_semder :
    forall g x w v,
      sem_value_derivation g (NT x) w v
      -> (exists ys p f vs,
             PM.MapsTo (x, ys) (@existT _ _ (x, ys) (p, f)) g
             /\ sem_values_derivation g ys w vs
             /\ f vs = v).
  Proof.
    intros g x w v hd.
    inversion hd as [| ? ? ? ? ? ? hm hd' hp h h' heq]; subst; clear hd.
    - repeat eexists; eauto.
      apply Eqdep_dec.inj_pair2_eq_dec in heq; auto.
      apply SymbolAsUOT.eq_dec.
  Qed.

  (** [sem_values_derivation] is closed under concatenation of symbol lists, token lists, and tuple concatenation. *)
  Lemma svd_app' :
    forall gr ys1 w1 vs1,
      sem_values_derivation gr ys1 w1 vs1
      -> forall ys2 w2 vs2,
        sem_values_derivation gr ys2 w2 vs2
        -> sem_values_derivation gr (ys1 ++ ys2) (w1 ++ w2) (concat_tuple _ _ vs1 vs2).
  Proof.
    intros gr ys1 w1 vs1 hd.
    induction hd; intros ys2 w2' vs2 hd2; simpl in *; auto.
    rewrite <- app_assoc; constructor; auto.
  Qed.

  (** Convenience wrapper for [svd_app']: concatenates two semantic derivations. *)
  Lemma svd_app :
    forall gr ys ys' w w' vs vs',
      sem_values_derivation gr ys w vs
      -> sem_values_derivation gr ys' w' vs'
      -> sem_values_derivation gr (ys ++ ys') (w ++ w') (concat_tuple _ _ vs vs').
  Proof.
    intros; eapply svd_app'; eauto.
  Qed.

  (** Strips a spurious empty-symbol-list append from a semantic values derivation. *)
  Lemma svd_app_nil_r' :
    forall gr ss w vs,
      sem_values_derivation gr (ss ++ []) w (concat_tuple ss [] vs tt)
      -> sem_values_derivation gr ss w vs.
  Proof.
    intros gr ss; induction ss as [| s ss IH]; intros w vs hd; sis.
    - inv hd.
      assert (vs = tt).
      { destruct vs; auto. }
      subst; auto.
    - inversion hd as [| ? ? ? ? ? ? hv hvs h h' h'' ]; subst; clear hd.
      apply symbols_semty_inj in h''.
      unfold concat_tuple_rec_case in h''.
      unfold eq_rect_r in h''.
      rewrite <- Eqdep_dec.eq_rect_eq_dec in h''.
      + destruct vs.
        inv h''.
        constructor; auto.
      + apply GammaAsUOT.eq_dec.
  Qed.

  (** Strips a spurious empty append on both the symbol list and token list sides. *)
  Lemma svd_app_nil_r :
    forall gr ss w vs,
      sem_values_derivation gr (ss ++ []) (w ++ []) (concat_tuple ss [] vs tt)
      -> sem_values_derivation gr ss w vs.
  Proof.
    intros gr ss w vs hd.
    assert (heq : w = w ++ []) by (rewrite app_nil_r; auto).
    rewrite <- heq in hd.
    apply svd_app_nil_r'; auto.
  Qed.

  (** Strips a spurious empty-token-list append from a semantic values derivation. *)
  Lemma svd_app_nil_r_word:
    forall gr ss w vs,
      sem_values_derivation gr ss (w ++ []) vs
      -> sem_values_derivation gr ss w vs.
  Proof.
    intros gr ss w vs hd.
    rewrite app_nil_r in hd; auto.
  Qed.

  (** Splits a semantic values derivation over a concatenated symbol list into two derivations. *)
    Lemma svd_split :
    forall g ys ys' w'' vs'',
      sem_values_derivation g (ys ++ ys') w'' vs''
      -> exists w w' vs vs',
        w'' = w ++ w'
        /\ vs'' = concat_tuple _ _ vs vs'
        /\ sem_values_derivation g ys w vs
        /\ sem_values_derivation g ys' w' vs'.
  Proof.
    intros g ys; induction ys as [| y ys Ih]; intros ys' w'' vs'' hvs; sis.
    - exists []; exists w''; exists tt; exists vs''; repeat split; auto.
    - inv_svs hvs hv hvs'; ss_inj. 
      apply Ih in hvs'.
      destruct hvs' as [w [w' [vs' [vs'' [? [? [hvs' hvs'']]]]]]]; subst.
      exists (w1 ++ w); exists w'; exists (v, vs'); exists vs''. 
      repeat split; auto; apps.
  Qed.
  
  (** Inversion on a singleton nonterminal semantic values derivation: extracts production and semantic data. *)
  Lemma svd_singleton_nt :
    forall g x w vs,
      sem_values_derivation g [NT x] w vs
      -> exists v ys vs' p f,
        vs = (v, tt)
        /\ PM.MapsTo (x, ys) (@existT _ _ (x, ys) (p, f)) g
        /\ sem_values_derivation g ys w vs'
        /\ p vs' = true
        /\ v = f vs'.
  Proof.
    intros g x w vs hd.
    inv_svs hd hs hd'; ss_inj.
    inv hs; s_inj.
    inv hd'; ss_inj.
    rew_anr; eauto 10.
  Qed.

  (** Inversion on a singleton terminal semantic values derivation: word is a singleton token and value a singleton tuple. *)
  Lemma svd_singleton_t :
    forall g a w vs,
      sem_values_derivation g [T a] w vs
      -> (exists v,
             w = [@existT _ _ a v]
             /\ vs = (v, tt)).
  Proof.
    intros g a w vs hd.
    inv_svs hd hs hd'.
    inv hs; inv hd'; s_inj; repeat ss_inj.
    rew_anr; eauto.
  Qed.

  (** Transfers a semantic values derivation along an equality of symbol lists. *)
  Lemma svd_eq :
    forall gr xs ys w vs vs'
           (heq  : xs = ys)
           (heq' : vs' = cast_ss xs ys heq vs),
      sem_values_derivation gr xs w vs
      -> sem_values_derivation gr ys w vs'.
  Proof.
    intros gr xs ys w vs vs' heq heq' hd.
    eapply cast_ss_prop_eq with (vs' := vs'); eauto.
  Qed.

  (** Inversion on a singleton semantic values derivation: extracts the single semantic value. *)
  Lemma svd_inv_singleton :
    forall g s w vs,
      sem_values_derivation g [s] w vs
      -> (exists v,
             (v, tt) = vs
             /\ sem_value_derivation g s w v).
  Proof.
    intros g s w vs hd; subst.
    inv_svs hd hv hvs; ss_inj.
    inv hvs; ss_inj.
    rew_anr; eauto.
  Qed.
  
  (** A single-symbol semantic derivation is equivalent to a singleton list semantic values derivation. *)
  Lemma svd_singleton :
    forall g s w v,
      sem_value_derivation g s w v
      <-> sem_values_derivation g [s] w (v, tt).
  Proof.
    intros g s w v; split; intros hd.
    - rew_nil_r w.
      constructor; auto.
    - apply svd_inv_singleton in hd.
      destruct hd as [v' [heq hd]].
      inv heq; auto.
  Qed.

  (** Splits a semantic derivation over a known append equality, distributing the cast. *)
  Lemma svd_split_eq :
    forall gr ys ys' ys'' w'' vs''
      (heq : ys'' = ys ++ ys'),
      sem_values_derivation gr ys'' w'' vs''
      -> (exists w w' vs vs',
             w'' = w ++ w'
             /\ cast_ss _ _ heq vs'' = concat_tuple _ _ vs vs'
             /\ sem_values_derivation gr ys w vs
             /\ sem_values_derivation gr ys' w' vs').
  Proof.
    intros gr ys ys' ys'' w'' vs'' heq hd; subst.
    apply svd_split in hd; auto.
  Qed.

  (** A semantic values derivation for the empty symbol list produces an empty word and unit tuple. *)
  Lemma svd_inv_nil_syms :
    forall gr ys w vs (heq : ys = []),
      sem_values_derivation gr ys w vs
      -> w = [] /\ cast_ss _ _ heq vs = tt.
  Proof.
    intros gr ys w vs heq hd; subst.
    inv hd; ss_inj.
    rewrite cast_ss_refl; auto.
  Qed.

  (** A semantic values derivation starting with a terminal must begin with the matching token. *)
  Lemma svd_inv_terminal_head :
    forall gr a ys ts vs,
      sem_values_derivation gr (T a :: ys) ts vs
      -> exists v ts', ts = @existT _ _ a v :: ts'.
  Proof.
    intros gr a ys ts vs hd; subst.
    inv hd; ss_inj.
    inv_t_der; s_inj.
    repeat eexists; split; eauto.
  Qed.

  (** Inversion on a semantic values derivation starting with a nonterminal head: decomposes the token list. *)
  Lemma svd_inv_nonterminal_head :
    forall gr x ys ys' ts vs v' vs' (heq : ys = NT x :: ys'),
      sem_values_derivation gr ys ts vs
      -> (v', vs') = cast_ss _ _ heq vs
      -> exists ts' ts'',
        ts = ts' ++ ts''
        /\ sem_value_derivation gr (NT x) ts' v'
        /\ sem_values_derivation gr ys' ts'' vs'.
  Proof.
    intros gr x ys ys' ts vs v' vs' heq hd heq'; subst.
    inv hd; ss_inj.
    rewrite cast_ss_refl in heq'; inv heq'; eauto.
  Qed.

  (** A terminal-headed symbol list cannot have an empty token derivation. *)
  Lemma svd_terminal_head_contra :
    forall gr a ys vs,
      ~ sem_values_derivation gr (T a :: ys) [] vs.
  Proof.
    unfold not; intros gr a ys vs hd.
    inv hd.
    match goal with
    | H : ?pre ++ ?suf = [] |- _ => apply app_eq_nil in H; destruct H; subst
    end.
    inv_t_der.
  Qed.

  (** Consuming a terminal token from the head of the derivation yields a derivation of the tail. *)
  Lemma svd_terminal_head__svd_tl :
    forall g ys a v ys' ts vs (heq : ys = T a :: ys'),
      sem_values_derivation g ys (@existT _ _ a v :: ts) vs
      -> (exists vs',
             (v, vs') = cast_ss _ _ heq vs
             /\ sem_values_derivation g ys' ts vs').
  Proof.
    intros g ys a v ys' ts vs ? hd; subst.
    inv_svs hd hh ht; ss_inj.
    inv hh; s_inj.
    sis; inv_cons_tokens_eq; t_inj.
    rewrite cast_ss_refl; eauto.
  Qed.
  
  (*
  Lemma svd_inv_terminal_head :
    forall gr a ys ys' ts vs v vs' (heq : ys = T a :: ys'),
      sem_values_derivation gr ys ts vs
      -> (v, vs') = cast_ss _ _ heq vs
      -> exists ts', ts = @existT _ _ a v :: ts' /\ sem_values_derivation gr (T a :: ys') (@existT _ _ a v :: ts') (v, vs').
  Proof.
    intros gr a ys ys' ts vs v vs' heq hd heq'; subst.
    rewrite cast_ss_refl in heq'.
    inv hd; ss_inj.
    inv_t_der; s_inj.
    inv_pr_eq; sis.
    eexists; split; eauto.
    rewrite cons_app_singleton with (x := @existT _ _ _ _).
    constructor; auto.
  Qed.                                              
   *)
  
  (** [tree_corresp_value g s w t v] jointly witnesses a tree derivation and a semantic value derivation for [s] in [g]. *)
  Inductive tree_corresp_value (g : grammar) :
    forall (s : symbol), list token -> tree -> symbol_semty s -> Prop :=
  | Leaf_corresp :
      forall (a : terminal)
             (v : t_semty a),
        tree_corresp_value g (T a) [@existT _ _ a v] (leaf a) v
  | Node_corresp :
      forall (x   : nonterminal)
             (ys  : list symbol)
             (w   : list token)
             (sts : forest)
             (vs  : symbols_semty ys)
             (p   : predicate_semty (x, ys))
             (f   : action_semty (x, ys)),
        PM.MapsTo (x, ys) (@existT _ _ (x, ys) (p,f)) g
        -> forest_corresp_values g ys w sts vs
        -> tree_corresp_value g (NT x) w (node x sts) (f vs)
  with forest_corresp_values (g : grammar) :
         forall (ys : list symbol), list token -> forest -> symbols_semty ys -> Prop :=
  | Nil_corresp :
      forest_corresp_values g [] [] [] tt
  | Cons_corresp :
      forall (s     : symbol)
             (ss    : list symbol)
             (w1 w2 : list token)
             (t     : tree)
             (ts    : forest)
             (v     : symbol_semty s)
             (vs    : symbols_semty ss),
        tree_corresp_value g s w1 t v
        -> forest_corresp_values g ss w2 ts vs
        -> forest_corresp_values g (s :: ss) (w1 ++ w2) (t :: ts) (v, vs).

  Hint Constructors tree_corresp_value forest_corresp_values : core.

  Scheme tcv_mutual_ind := Induction for tree_corresp_value Sort Prop
    with fcv_mutual_ind := Induction for forest_corresp_values Sort Prop.

  (** Inversion on a terminal [tree_corresp_value]: the tree is a leaf and the word a singleton token. *)
  Lemma inv_terminal_corresp :
    forall g a w t v,
      tree_corresp_value g (T a) w t v
      -> (w = [@existT _ _ a v]
          /\ t = leaf a).
  Proof.
    intros g a w t v hc.
    inv hc.
    apply Eqdep_dec.inj_pair2_eq_dec in H3; subst; auto.
    apply SymbolAsUOT.eq_dec.
  Qed.

  (** Inversion on a nonterminal [tree_corresp_value]: exposes the production, tree, and sub-values. *)
  Lemma inv_nonterminal_corresp :
    forall g x w t v,
      tree_corresp_value g (NT x) w t v
      -> (exists ys o f sts vs,
             PM.MapsTo (x, ys) (@existT _ _ (x, ys) (o, f)) g
             /\ t = node x sts
             /\ v = f vs
             /\ forest_corresp_values g ys w sts vs).
  Proof.
    intros g x w t v hc.
    inv hc.
    repeat eexists; eauto.
    apply Eqdep_dec.inj_pair2_eq_dec in H4; auto.
    apply SymbolAsUOT.eq_dec.
  Qed.

  (** A semantic derivation can always be witnessed by a corresponding [tree_corresp_value]. *)
  Lemma sem_derivation__exists_corresp_tree_derivation :
    forall g s w v,
      sem_value_derivation g s w v
      -> exists t, tree_corresp_value g s w t v.
  Proof.
    intros g s w v hs.
    induction hs using sem_value_derivation_mutual_ind with
        (P  := fun s w v hs =>
                 exists t, tree_corresp_value g s w t v)
        (P0 := fun ss w vs hs =>
                 exists ts, forest_corresp_values g ss w ts vs); eauto.
    - destruct IHhs as [sts hc].
      eexists; eauto.
    - destruct IHhs  as [st hc].
      destruct IHhs0 as [sts hc'].
      exists (st :: sts); auto.
  Qed.

  (** A semantic values derivation can always be witnessed by a corresponding [forest_corresp_values]. *)
  Lemma svd__exists_corresp_forest_derivation :
    forall g ys w vs,
      sem_values_derivation g ys w vs
      -> exists ts, forest_corresp_values g ys w ts vs.
  Proof.
    intros g ys w vs hs.
    induction hs using sem_values_derivation_mutual_ind with
        (P  := fun s w v hs =>
                 exists t, tree_corresp_value g s w t v)
        (P0 := fun ss w vs hs =>
                 exists ts, forest_corresp_values g ss w ts vs); eauto.
    - destruct IHhs as [sts hc].
      eexists; eauto.
    - destruct IHhs  as [st hc].
      destruct IHhs0 as [sts hc'].
      exists (st :: sts); auto.
  Qed.

(*  Lemma inv_nt_tcv :
    forall x t v,
      tree_corresp_value (NT x) t v
      -> (exists ys sts vs f,
             t = node x sts
             /\ forest_corresp_values ys sts vs
             /\ v = f vs).
  Proof.
    intros x t v hc.
    inversion hc as [| ? ? ? ? ? ? h h' heq]; subst; clear hc.
    repeat eexists; eauto.
    apply Eqdep_dec.inj_pair2_eq_dec in heq; eauto.
    apply SymbolAsUOT.eq_dec.
  Qed.
  
 *)

  (** A [tree_corresp_value] implies the underlying [tree_derivation]. *)
  Lemma corresp__tree_derivation :
    forall g s w t v,
      tree_corresp_value g s w t v
      -> tree_derivation g s w t.
  Proof.
    intros g s w t v hc.
    induction hc using tcv_mutual_ind with
        (P0 := fun ss w ts vs hc =>
                 forest_derivation g ss w ts); eauto.
    econstructor; eauto.
    eapply pm_mapsto_in; eauto.
  Qed.
    
  (** A [forest_corresp_values] implies the underlying [forest_derivation]. *)
  Lemma corresp__forest_derivation :
    forall g ss w ts vs,
      forest_corresp_values g ss w ts vs
      -> forest_derivation g ss w ts.
  Proof.
    intros g ss w ts vs hc.
    induction hc using fcv_mutual_ind with
        (P  := fun s w t v hc =>
                 tree_derivation g s w t); eauto.
    econstructor; eauto.
    eapply pm_mapsto_in; eauto.
  Qed.

  (** A semantic values derivation implies the existence of a corresponding forest derivation. *)
  Lemma svd__exists_forest_der :
    forall gr ys w vs,
      sem_values_derivation gr ys w vs
      -> exists ts, forest_derivation gr ys w ts.
  Proof.
    intros gr ys w vs hs.
    apply svd__exists_corresp_forest_derivation in hs.
    destruct hs as [ts hfcv].
    apply corresp__forest_derivation in hfcv; eauto.
  Qed.

  (** A reversed semantic values derivation implies the existence of a reversed forest derivation. *)
  Lemma svd__exists_rev_forest_der :
    forall gr ys w vs,
      sem_values_derivation gr (rev ys) w (rev_tuple _ vs)
      -> exists ts, forest_derivation gr (rev ys) w (rev ts).
  Proof.
    intros gr ys w vs hs.
    apply svd__exists_corresp_forest_derivation in hs.
    destruct hs as [ts hfcv].
    apply corresp__forest_derivation in hfcv.
    exists (rev ts).
    rewrite rev_involutive; auto.
  Qed.

  (** If two [forest_corresp_values] produce the same forest with matching suffixes, the prefixes and symbol lists are equal. *)
  Lemma fcv__forests_eq__words_eq_rhss_eq :
    forall g ss ss' pre pre' suf suf' ts vs vs',
      forest_corresp_values g ss pre ts vs
      -> forest_corresp_values g ss' pre' ts vs'
      -> pre ++ suf = pre' ++ suf'
      -> pre' = pre /\ suf' = suf /\ ss' = ss.
  Proof.
    intros g ss ss' pre pre' suf suf' ts vs vs' hc hc' heq.
    apply corresp__forest_derivation in hc.
    apply corresp__forest_derivation in hc'.
    eapply forests_eq__words_eq_rhss_eq; eauto.
  Qed.

  (** Two [tree_corresp_value] witnesses for the same tree with consistent suffix extensions agree on value and word. *)
  Lemma tree_corresp_values_function' :
    forall (g      : grammar)
           (s : symbol)
           (pre : list token)
           (t : tree)
           (v : symbol_semty s),
      tree_corresp_value g s pre t v
      -> (forall (pre' suf suf' : list token)
                 (v' : symbol_semty s),
             tree_corresp_value g s pre' t v'
             -> pre ++ suf = pre' ++ suf'
             -> pre = pre' /\ suf = suf' /\ v = v').
  Proof.
    intros g s pre t v hc.
    induction hc using tcv_mutual_ind with
        (P  := fun s pre t v hc =>
                 (forall pre' suf suf' v',
                     tree_corresp_value g s pre' t v'
                     -> pre ++ suf = pre' ++ suf'
                     -> pre = pre' /\ suf = suf' /\ v = v'))
        (P0 := fun ss pre ts vs hc =>
                 (forall pre' suf suf' vs',
                     forest_corresp_values g ss pre' ts vs'
                     -> pre ++ suf = pre' ++ suf'
                     -> pre = pre' /\ suf = suf' /\ vs = vs')).
    - intros wpre' wsuf wsuf' v' hc heq.
      apply inv_terminal_corresp in hc.
      destruct hc; subst.
      inv heq.
      apply Eqdep_dec.inj_pair2_eq_dec in H1; subst; auto.
      apply t_eq_dec.
    - intros wpre' wsuf wsuf' v' hc heq.
      apply inv_nonterminal_corresp in hc.
      destruct hc as [ys' [p' [f' [sts' [vs' [hm [heq' [heq'' hc]]]]]]]]; subst.
      inv heq'.
      pose proof hc as hc'.
      eapply fcv__forests_eq__words_eq_rhss_eq
        with (ss := ys) in hc; subst; eauto.
      destruct hc as [? [? ?]]; subst.
      repeat split; auto.
      eapply IHhc in hc'; eauto.
      destruct hc' as [_ [_ ?]]; subst.
      apply PMF.MapsTo_fun
        with (e := @existT _ _ (x,ys) (p,f)) in hm; auto.
      apply Eqdep_dec.inj_pair2_eq_dec in hm.
      + inv hm; auto.
      + apply ProductionAsUOT.eq_dec.
    - intros pre suf suf' vs' hc heq; sis; subst.
      inv hc; repeat split; auto.
      apply Eqdep_dec.inj_pair2_eq_dec in H2; auto.
      apply GammaAsUOT.eq_dec.
    - intros wpre' wsuf wsuf' vs' hc' heq.
      inv hc'.
      repeat rewrite <- app_assoc in heq.
      eapply IHhc in H5; eauto.
      destruct H5 as [? [? ?]]; subst.
      eapply IHhc0 in H6; eauto.
      destruct H6 as [? [? ?]]; subst.
      repeat split; auto.
      apply Eqdep_dec.inj_pair2_eq_dec in H3; auto.
      apply GammaAsUOT.eq_dec.
  Qed.

  (** The semantic value in a [tree_corresp_value] is uniquely determined by the grammar, symbol, word, and tree. *)
  Lemma tree_corresp_value_function :
    forall (g : grammar)
           (s : symbol)
           (w : list token)
           (t : tree)
           (v v' : symbol_semty s),
      tree_corresp_value g s w t v
      -> tree_corresp_value g s w t v'
      -> v = v'.
  Proof.
    intros g s w t v v' hc hc'.
    eapply tree_corresp_values_function'
      with (suf := []) (suf' := []) (v := v) in hc'; eauto.
    firstorder.
  Qed.
  
  (** If there is a unique parse tree, then the semantic value is also unique. *)
  Lemma all_trees_eq__all_sem_values_eq :
    forall g s w v t,
      sem_value_derivation g s w v
      -> tree_corresp_value g s w t v
      -> (forall t', tree_derivation g s w t' -> t' = t)
      -> (forall v', sem_value_derivation g s w v' -> v = v').
  Proof.
    intros g s w v t hd hc hu v' hd'.
    apply sem_derivation__exists_corresp_tree_derivation in hd'.
    destruct hd' as [t' hc'].
    pose proof hc' as hc''.
    apply corresp__tree_derivation in hc''.
    apply hu in hc''; subst.
    eapply tree_corresp_value_function; eauto.
  Qed.
  
  (** [sym_recognize g s w] holds when [w] is a word recognized by symbol [s] in grammar [g], ignoring semantic values. *)
  Inductive sym_recognize (g : grammar) : symbol -> list token -> Prop :=
  | T_rec  : 
      forall (a : terminal) (l : t_semty a),
        sym_recognize g (T a) [@existT _ _ a l]
  | nt_rec : 
      forall (x  : nonterminal) (ys : list symbol) (w : list token),
        PM.In (x, ys) g
        -> gamma_recognize g ys w
        -> sym_recognize g (NT x) w
  with gamma_recognize (g : grammar) : list symbol -> list token -> Prop :=
       | Nil_rec  : 
           gamma_recognize g [] []
       | Cons_rec : 
           forall (s : symbol) (ss : list symbol) (wpre wsuf : list token),
             sym_recognize g s wpre
             -> gamma_recognize g ss wsuf
             -> gamma_recognize g (s :: ss) (wpre ++ wsuf).

  Hint Constructors sym_recognize gamma_recognize : core.

  Ltac inv_sr hs  hi hg :=
    inversion hs as [ ? ? | ? ? ? hi hg ]; subst; clear hs.

  Ltac inv_gr hg  wpre wsuf hs hg' :=
    inversion hg as [| ? ? wpre wsuf hs hg']; subst; clear hg.

  Scheme sym_recognize_mutual_ind   := Induction for sym_recognize Sort Prop
    with gamma_recognize_mutual_ind := Induction for gamma_recognize Sort Prop.

  (** A tree derivation implies recognition by the same symbol. *)
  Lemma tree_derivation__sym_recognize :
    forall g s w v,
      tree_derivation g s w v
      -> sym_recognize g s w.
  Proof.
    intros g ys w v hs.
    induction hs using tree_derivation_mutual_ind
      with (P0 := fun ys w f (hg : forest_derivation g ys w f) => 
                    gamma_recognize g ys w); eauto.
  Qed.

  (** A gamma recognition starting with a terminal must consume the matching token first. *)
  Lemma gamma_recognize_terminal_head :
    forall g a suf w,
      gamma_recognize g (T a :: suf) w
      -> exists l w',
        w = (@existT _ _ a l) :: w'
        /\ gamma_recognize g suf w'.
  Proof.
    intros g a suf w hg.
    inversion hg as [| h t wpre wsuf hs hg']; subst; clear hg.
    inv hs; simpl; eauto.
  Qed.

  (** A gamma recognition starting with a nonterminal splits the word into a production-derived prefix and suffix. *)
  Lemma gamma_recognize_nonterminal_head :
    forall g x suf w,
      gamma_recognize g (NT x :: suf) w
      -> exists rhs wpre wsuf,
        w = wpre ++ wsuf
        /\ PM.In (x, rhs) g
        /\ gamma_recognize g rhs wpre
        /\ gamma_recognize g suf wsuf.
  Proof.
    intros g x suf w hg.
    inversion hg as [| h t wpre wsuf hs hg']; subst; clear hg.
    inv hs; simpl; eauto 8.
  Qed.

  (** [gamma_recognize] is closed under concatenation of symbol lists and token lists. *)
  Lemma gamma_recognize_app' :
    forall g ys1 w1,
      gamma_recognize g ys1 w1
      -> forall ys2 w2,
        gamma_recognize g ys2 w2
        -> gamma_recognize g (ys1 ++ ys2) (w1 ++ w2).
  Proof.
    intros g ys1 w1 hg.
    induction hg; intros ys2 w2 hg2; simpl in *; auto.
    rewrite <- app_assoc; constructor; auto.
  Qed.

  (** Convenience wrapper for [gamma_recognize_app']: appends two gamma recognitions. *)
  Lemma gamma_recognize_app :
    forall g ys1 ys2 w1 w2,
      gamma_recognize g ys1 w1
      -> gamma_recognize g ys2 w2
      -> gamma_recognize g (ys1 ++ ys2) (w1 ++ w2).
  Proof.
    intros; apply gamma_recognize_app'; auto.
  Qed.

  (** Splits a gamma recognition over a concatenated symbol list into two recognitions. *)
  Lemma gamma_recognize_split :
    forall g ys ys' w'',
      gamma_recognize g (ys ++ ys') w''
      -> exists w w',
        w'' = w ++ w'
        /\ gamma_recognize g ys w
        /\ gamma_recognize g ys' w'.
  Proof.
    intros g ys; induction ys as [| y ys Ih]; intros ys' w'' hg; sis.
    - exists []; exists w''; repeat split; auto.
    - inversion hg as [| s ss wpre wsuf hs hg']; subst; clear hg. 
      apply Ih in hg'; destruct hg' as [w [w' [? [hg' hg'']]]]; subst.
      exists (wpre ++ w); exists w'; repeat split; auto; apps.
  Qed.

  (** Folds a nonterminal's RHS recognition back into a recognition of the nonterminal head. *)
  Lemma gamma_recognize_fold_head_nt :
    forall g x rhs ys ts,
      PM.In (x, rhs) g
      -> gamma_recognize g (rhs ++ ys) ts
      -> gamma_recognize g (NT x :: ys) ts.
  Proof.
    intros g x rhs ys ts hi hr.
    apply gamma_recognize_split in hr.
    destruct hr as [w [w' [? [hr hr']]]]; subst; eauto.
  Qed.

  (** A forest derivation implies gamma recognition with the same symbol list and word. *)
  Lemma forest_derivation__gamma_recognize :
    forall g ys w v,
      forest_derivation g ys w v
      -> gamma_recognize g ys w.
  Proof.
    intros g ys w v hg.
    induction hg using forest_derivation_mutual_ind with
        (P := fun s w t (hs : tree_derivation g s w t) => 
                sym_recognize g s w); eauto.
  Qed.

  (** Gamma recognition implies the existence of a forest derivation (existence, not uniqueness). *)
  Lemma gamma_recognize__exists_forest_derivation :
    forall g ys w,
      gamma_recognize g ys w
      -> exists v,
        forest_derivation g ys w v.
  Proof.
    intros g ys w hg.
    induction hg using gamma_recognize_mutual_ind with
        (P := fun s w (hs : sym_recognize g s w) => 
                exists t, tree_derivation g s w t);
      firstorder; repeat econstructor; eauto.
  Qed.

  (* A stronger, predicate-aware notion of what it means 
     for the stack to accept the remaining input. For the 
     semantic predicate/action version of CoStar, we use 
     this definition in place of the "remaining symbols 
     recognize the remaining input" invariant. *)
  
  (** Holds when the current semantic values [vs] for symbols [ss] can be extended through the tail frames
      to produce a valid derivation for the remaining input [w]. *)
  Fixpoint lower_frames_accept_suffix
           (gr  : grammar)
           (ss  : list symbol)
           (vs  : symbols_semty ss)
           (frs : list parser_frame)
           (w   : list token) : Prop :=
    match frs with
    | [] => w = []
    | Fr pre vs_pre (NT x :: suf) :: frs' =>
      (exists wpre wsuf vs_suf p f,
          w = wpre ++ wsuf
          /\ sem_values_derivation gr suf wpre vs_suf
          /\ PM.MapsTo (x, ss) (@existT _ _ (x, ss) (p, f)) gr
          /\ p vs = true
          /\ lower_frames_accept_suffix gr
                                        (rev pre ++ NT x :: suf)
                                        (concat_tuple (rev pre) (NT x :: suf) (rev_tuple _ vs_pre) (f vs, vs_suf))
                                        frs'
                                        wsuf)
    | _ => True
    end.

  (** [lower_frames_accept_suffix] is preserved under equal (up to cast) symbol list and semantic values. *)
  Lemma lfas_eq :
    forall gr ys ys' vs vs' frs ts (heq : ys = ys'),
      vs' = cast_ss _ _ heq vs
      -> lower_frames_accept_suffix gr ys vs frs ts
      -> lower_frames_accept_suffix gr ys' vs' frs ts.
  Proof.
    intros gr ys ys' vs vs' frs ts ? ? hl; subst.
    rewrite cast_ss_refl; auto.
  Qed.
  
  (** If the head value is replaced by an equal value, [lower_frames_accept_suffix] still holds. *)
  Lemma lfas_replace_head :
    forall gr ys x zs vs v v' vs'' frs w,
      lower_frames_accept_suffix gr (ys ++ NT x :: zs) (concat_tuple ys (NT x :: zs) vs (v, vs'')) frs w
      -> v = v'
      -> lower_frames_accept_suffix gr (ys ++ NT x :: zs) (concat_tuple ys (NT x :: zs) vs (v', vs'')) frs w.
  Proof.
    intros; subst; auto.
  Qed.

  (** The key invariant: a parser stack [sk] accepts suffix [w] if the stack's semantic values can be
      extended to a complete derivation of the full remaining input [w]. *)
  Definition stack_accepts_suffix (gr : grammar) (sk : parser_stack) (w : list token) : Prop :=
    match sk with
    | (Fr pre vs_pre suf, frs) =>
      (exists wpre wsuf vs_suf,
          w = wpre ++ wsuf
          /\ sem_values_derivation gr suf wpre vs_suf
          /\ lower_frames_accept_suffix gr
                                        (rev pre ++ suf)
                                        (concat_tuple (rev pre) suf (rev_tuple pre vs_pre) vs_suf)
                                        frs
                                        wsuf)
       end.

  (* General-purpose tactic for solving equalities with dependent types *)
  Ltac t :=
    match goal with
    | |- context[rev_tuple_cons_case] =>
      unrt
    | |- lower_frames_accept_suffix _ _ (concat_tuple _ _ _ ((cast_action _ _ _ _) _, _)) _ _ =>
      eapply lfas_replace_head; eauto
    | |- concat_tuple ?xs ?ys ?vx ?vy = cast_ss (?xs' ++ ?ys) (?xs ++ ?ys) ?pf (concat_tuple ?xs' ?ys ?vx' ?vy') =>
      eapply concat_tuple_eq with (heq := app_inv_tail  _ _ _ pf)
    | |- concat_tuple ?pre (?s :: ?suf) _ _ = cast_ss _ _ _ (concat_tuple ?pre' ([?s] ++ ?suf) _ _) =>
      eapply concat_tuple_eq
    | |- context[cast_ss ?xs ?xs _ _] =>
      rewrite cast_ss_refl
    | |- (?a, ?b) = (?a', ?b') =>
      apply pair_split_eq
    | |- ?f ?vs = (cast_action _ _ _ ?f) ?vs' =>
      eapply cast_action_eq
    | |- context[concat_tuple (rev (rev ?xs)) []] =>
      erewrite rrt_anr
    | |- (cast_predicate _ _ _ _) _ = true =>
      eapply cast_predicate_eq_true; eauto
    | |- context[concat_tuple (_ ++ [_]) _ (concat_tuple _ [_] _ _) _] => erewrite concat_tuple_assoc'
    | |- context[cast_ss _ _ _ (cast_ss _ _ _ _)] =>
      erewrite <- cast_ss_ins_trans
    | |- context[rev_tuple _ (rev_tuple _ _)] =>
      erewrite rev_tuple_involutive
    | |- PM.MapsTo _ (@existT _ _ _ (cast_predicate _ _ _ _, cast_action _ _ _ _)) _ =>
      eapply mapsto_cast; eauto
    end.

  Ltac t' := repeat t.
  
  (** Performing a return step (completing a production) preserves [stack_accepts_suffix]. *)
  Lemma return_preserves_sas :
    forall gr ce cr cr' pre' vs' pre vs x suf frs p f ts,
      ce = Fr pre' vs' []
      -> cr = Fr pre vs (NT x :: suf)
      -> cr' = Fr (NT x :: pre) (f (rev_tuple _ vs'), vs) suf
      -> PM.MapsTo (x, rev pre') (@existT _ _ (x, rev pre') (p, f)) gr
      -> p (rev_tuple _ vs') = true
      -> stack_accepts_suffix gr (ce, cr :: frs) ts
      -> stack_accepts_suffix gr (cr', frs) ts.
  Proof.
    intros gr ce cr cr' pre' vs' pre vs x suf frs p f ts ? ? ? hm hp hs; subst; sis.
    destruct hs as (wpre & wsuf & vs_suf & heq & hd & hex); subst.
    destruct hex as (wsuf' & wsuf'' & vs_suf' & p' & f' & heq & hd' & hm' & hp' & hl); subst.
    destruct vs_suf.
    apply svd_inv_nil_syms in hd; subst; sis; auto.
    exists wsuf'; exists wsuf''; eexists; repeat split; eauto.
    t'; sis; repeat unct.
    eapply lfas_eq; eauto.
    eapply lfas_replace_head; eauto.
    eapply mapsto_cast with (x' := (x, rev pre'))
                            (z  := (x, rev pre')) in hm'; eauto; apps.
    eapply PMF.MapsTo_fun with (e := @existT _ _ (x, rev pre') (p, f)) in hm'; auto.
    apply inv_grammar_entry_eq in hm'.
    destruct hm' as [hpeq hfeq].
    rewrite hfeq.
    t'.
    erewrite concat_tuple_nil_r; eauto.
    t'; auto.
    Unshelve.
    all : apps.
  Qed.

  (** Consuming a terminal token from the head frame preserves [stack_accepts_suffix]. *)
  Lemma consume_preserves_sas :
    forall gr fr fr' frs pre a v vs suf ts,
      fr = Fr pre vs (T a :: suf)
      -> fr' = Fr (T a :: pre) (v, vs) suf
      -> stack_accepts_suffix gr (fr, frs) (@existT _ _ a v :: ts)
      -> stack_accepts_suffix gr (fr', frs) ts.
  Proof.
    intros gr fr fr' frs pre a v vs suf ts ? ? hs; subst.
    red in hs.
    destruct hs as (wpre & wsuf & vs_suf & heq & hd & hl); subst.
    pose proof hd as hd'.
    apply svd_inv_terminal_head in hd.
    destruct hd as (v' & ts' & heq'); subst.
    inv_svs hd' hh ht; ss_inj.
    inv_sv hh hm hvs hp; s_inj; sis.
    inv_cons_tokens_eq; t_inj.
    inv heq; t_inj.
    exists ts'; exists wsuf; eexists; repeat split; eauto.
    eapply lfas_eq; eauto.
    t'.
    eapply cast_elim_common.
    t'; auto; sis.
    t'; repeat unct; auto.
    Unshelve.
    all : apps.
  Qed.

  (** A cast predicate applied to cast values cannot differ from the original predicate on original values. *)
  Lemma failed_predicate_contra :
    forall x ys ys' (p : predicate_semty (x, ys)) (p' : predicate_semty (x, ys')) vs vs'
           (heq : ys = ys') (heq' : (x, ys) = (x, ys')),
      vs' = cast_ss _ _ heq vs
      -> p' = cast_predicate _ _ heq' p
      -> ~ p vs <> p' vs'.
  Proof.
    intros x ys ys' p p' vs vs' ? ? ? ?; subst.
    unfold not; intros hp.
    apply hp.
    rewrite cast_predicate_refl.
    rewrite cast_ss_refl; auto.
  Qed.
    
  (** If the stack accepts a suffix then the predicate for the completing production cannot be false. *)
  Lemma sas_failed_predicate_contra :
    forall gr ce cr pre' vs' pre vs x suf frs p f ts,
      ce = Fr pre' vs' []
      -> cr = Fr pre vs (NT x :: suf)
      -> stack_accepts_suffix gr (ce, cr :: frs) ts
      -> PM.MapsTo (x, rev pre') (@existT _ _ (x, rev pre') (p, f)) gr
      -> p (rev_tuple _ vs') <> false.
  Proof.
    intros gr ce cr pre' vs' pre vs x suf frs p f ts ? ? hs hm hp; subst.
    red in hs.
    destruct hs as (wpre & wsuf & vs_suf & heq & hd & hl); subst; sis.
    destruct hl as (wsuf' & wsuf'' & vs_suf' & p' & f' & heq & hd' & hm' & hp' & hl); subst.
    destruct vs_suf.
    eapply failed_predicate_contra with
        (x := x)
        (p := p)
        (vs := rev_tuple _ vs')
        (p' := p')
        (vs'  := concat_tuple _ [] (rev_tuple _ vs') tt); tc.
    - erewrite concat_tuple_nil_r; eauto.
    - eapply mapsto_cast with (x' := (x, rev pre'))
                              (z  := (x, rev pre')) in hm'; eauto; apps.
      eapply PMF.MapsTo_fun with (e := @existT _ _ (x, rev pre') (p, f)) in hm'; auto.
    apply inv_grammar_entry_eq in hm'.
    destruct hm' as [hpeq hfeq].
    rewrite hpeq.
    rewrite cast_predicate_roundtrip; auto.
    Unshelve.
    all : apps.
  Qed.

  (** If the stack accepts a suffix and the head frame has a nonterminal suffix, the nonterminal is in the rhs_map. *)
  Lemma sas_find_neq_none :
    forall gr rm cr pre vs x suf frs ts,
      cr = Fr pre vs (NT x :: suf)
      -> rhs_map_correct rm gr
      -> stack_accepts_suffix gr (cr, frs) ts
      -> NM.find x rm <> None.
  Proof.
    intros gr rm cr pre vs x suf frs ts ? hr hs hf; subst.
    destruct hs as (wpre & wsuf & vs_suf & heq & hd & hl); subst; sis.
    inv_svs hd hh ht.
    inv_sv hh hm hvs hp.
    apply pm_mapsto_in in hm.
    destruct hr as (_ & _ & hc).
    apply hc in hm.
    destruct hm as [yss [hm hi]].
    apply NMF.find_mapsto_iff in hm; tc.
  Qed.

  (* Inductive definition of a nullable grammar symbol *)
  (** [nullable_sym g s] holds when [s] can derive the empty word in [g]. *)
  Inductive nullable_sym (g : grammar) : symbol -> Prop :=
  | nullable_nt : forall x ys,
      PM.In (x, ys) g
      -> nullable_gamma g ys
      -> nullable_sym g (NT x)
  with nullable_gamma (g : grammar) : list symbol -> Prop :=
       | nullable_nil  : nullable_gamma g []
       | nullable_cons : forall hd tl,
           nullable_sym g hd
           -> nullable_gamma g tl
           -> nullable_gamma g (hd :: tl).

  Hint Constructors nullable_sym nullable_gamma : core.

  (** A concatenation is nullable iff both parts are nullable. *)
  Lemma nullable_split :
    forall g xs ys,
      nullable_gamma g (xs ++ ys)
      -> nullable_gamma g xs /\ nullable_gamma g ys.
  Proof.
    intros g xs; induction xs as [| x xs Ih]; intros ys hn; sis; auto.
    inv hn; firstorder.
  Qed.

  (** The right part of a nullable concatenation is itself nullable. *)
  Lemma nullable_split_l :
    forall g xs ys,
      nullable_gamma g (xs ++ ys)
      -> nullable_gamma g ys.
  Proof.
    intros g xs ys hn; apply nullable_split in hn; firstorder.
  Qed.

  (** Two nullable sequences can be concatenated to form a nullable sequence. *)
  Lemma nullable_app :
    forall g xs ys,
      nullable_gamma g xs
      -> nullable_gamma g ys
      -> nullable_gamma g (xs ++ ys).
  Proof.
    intros g xs ys hng hng'.
    induction xs as [| x xs]; sis; inv hng; auto.
  Qed.

  (** [nullable_path g x y] holds when [x] can reach [y] through a sequence of nullable nonterminal expansions. *)
  Inductive nullable_path (g : grammar) :
    symbol -> symbol -> Prop :=
  | direct_path : forall x z gamma pre suf,
      PM.In (x, gamma) g
      -> gamma = pre ++ NT z :: suf
      -> nullable_gamma g pre
      -> nullable_path g (NT x) (NT z)
  | indirect_path : forall x y z gamma pre suf,
      PM.In (x, gamma) g
      -> gamma = pre ++ NT y :: suf
      -> nullable_gamma g pre
      -> nullable_path g (NT y) (NT z)
      -> nullable_path g (NT x) (NT z).

  Hint Constructors nullable_path : core.

  (** [nullable_path] is transitive: paths can be chained. *)
  Lemma nullable_path_trans :
    forall g x y z,
      nullable_path g x y
      -> nullable_path g y z
      -> nullable_path g x z.
  Proof.
    intros g x y z hxy hyz.
    induction hxy; sis; subst.
    - destruct z as [a | z]; eauto.
      inv hyz.
    - destruct z as [a | z]; eauto.
      inv hyz.
  Qed.  

  (** A symbol is left-recursive in [g] if it can reach itself via a nullable path. *)
  Definition left_recursive g sym :=
    nullable_path g sym sym.

  (** A grammar has no left recursion if no nonterminal is left-recursive. *)
  Definition no_left_recursion g :=
    forall (x : nonterminal),
      ~ left_recursive g (NT x).

End DefsFn.

Module Type DefsT (SymTy : SymbolTypes).
  Include DefsFn SymTy.
End DefsT.

Module Type T.
  Declare Module SymTy : SymbolTypes.
  Declare Module Defs  : DefsT SymTy.
  Export SymTy.
  Export Defs.
End T.
