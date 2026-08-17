(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.

From Stdlib Require Import FSets FSets.FMapAVL FSets.FMapFacts.
From Stdlib Require Import ZArith.BinInt.

From Crane.Libraries.ParseALot.Utils Require Import Ltac.
From Crane.Libraries.ParseALot.Lexer Require Import Regex.
From Crane.Libraries.ParseALot.Utils Require Import Orders.


(** Module type for token labels: a type with decidable equality and a default element. *)
Module Type Label.

  Parameter Label : Type.
  Parameter defLabel : Label.
  Parameter Label_eq_dec : forall (l l' : Label), {l = l'} + {l <> l'}.

End Label.

(** Module type specifying the interface of a DFA-like state machine over a regex alphabet [R]. *)
Module Type State (Import R : Regex.T).

  Import R.Ty.

  (*** Core ***)

  (* The labels for lexical rules; this should probably be defined somewhere else *)
  Parameter Label : Type.
  Parameter Label_eq_dec : forall (l l' : Label), {l = l'} + {l <> l'}.
  Parameter defLabel : Label.

  (* Pointers are like state-labels for state machines *)
  Parameter Pointer : Type.
  Parameter defPointer : Pointer.
  Parameter pointer_compare : Pointer -> Pointer -> comparison.
  Parameter pointer_compare_eq : forall x y,
      pointer_compare x y = Eq <-> x = y.
  Parameter pointer_compare_trans : forall c x y z,
      pointer_compare x y = c -> pointer_compare y z = c -> pointer_compare x z = c.

  (* Delta is some mechanism for transitioning, like a transition table *)
  Parameter Delta : Type.
  Parameter defDelta : Delta.

  (* A State tells you where you are in the machine and how to transition *)
  (** A [State] pairs a control [Pointer] with a transition table [Delta]. *)
  Definition State : Type := prod Pointer Delta.
  (** The default (initial) state using default pointer and delta. *)
  Definition defState : State := (defPointer, defDelta).


  (*** Index ***)
  Parameter index : Type.
  Parameter index0 : index.
  Parameter index_eq_dec : forall (i ii : index), {i = ii} + {i <> ii}.
  Parameter incr : index -> index.
  Parameter decr : index -> index.
  Parameter init_index : nat -> index.

  Parameter index2list : index -> list bool.
  Parameter list2index : list bool -> index.
  Parameter list_inv : forall (x : index), list2index (index2list x) = x.

  (* for index correctness *)
  Parameter decr_inv_incr : forall i, decr (incr i) = i.
  Parameter incr_inv_decr : forall i, incr (decr i) = i.
  Parameter decr_inv_S : forall n, decr (init_index (S n)) = init_index n.
  Parameter incr_is_S : forall n, init_index (S n) = incr (init_index n).
  Parameter n_det_index : forall n1 n2, init_index n1 = init_index n2 -> n1 = n2.


  (*** State Machine ***)
  Parameter transition : Sigma -> State -> State.
  Parameter transition_list : list Sigma -> State -> State.
  Parameter transition_list_nil : forall fsm,
      transition_list [] fsm = fsm.
  Parameter transition_list_cons : forall bs a fsm,
      transition_list (a :: bs) fsm = transition_list bs (transition a fsm).
  Parameter transition_Delta : forall a p p' d d',
      transition a (p, d) = (p', d') -> d = d'.

  Parameter accepts : String -> State -> bool.
  Parameter accepting : State -> bool.

  Parameter accepts_nil: forall fsm, accepting fsm = accepts [] fsm.
  Parameter accepts_transition : forall cand a fsm,
      accepts cand (transition a fsm) = accepts (a :: cand) fsm.

  Parameter init_state : regex -> State.
  Parameter init_state_inv : State -> regex.

  Parameter invert_init_correct : forall r s,
      exp_match s (init_state_inv (init_state r)) <-> exp_match s r.

  Parameter accepting_dt_list : forall bs e,
      accepting (transition_list bs (init_state e))
      = accepting (init_state (derivative_list bs e)).

  Parameter accepts_matches : forall(s : String) (e : regex),
      true = accepts s (init_state e) <-> exp_match s e.

End State.


(** Functor instantiating state-machine definitions (prefixes, tokens, max-munch spec) over [R] and [Ty]. *)
Module DefsFn (R : Regex.T) (Ty : State R).

  Import Ty.
  Import R.Defs.
  Import R.Ty.

  (** Wraps [Pointer] as a [UsualComparableType] for ordered-set functors. *)
  Module Pointer_as_UCT <: UsualComparableType.
    Definition t := Pointer.
    Definition compare := pointer_compare.
    Definition compare_eq := pointer_compare_eq.
    Definition compare_trans := pointer_compare_trans.

    (** Decidable equality on [Pointer] derived from [pointer_compare]. *)
    Lemma Pointer_eq_dec : forall (x y : Pointer), {x = y} + {x <> y}.
    Proof.
      intros. destruct (pointer_compare x y) eqn:E.
      - apply pointer_compare_eq in E. auto.
      - right. intros C. apply pointer_compare_eq in C. rewrite C in *. discriminate.
      - right. intros C. apply pointer_compare_eq in C. rewrite C in *. discriminate.
    Qed.

  End Pointer_as_UCT.

  (** Core type aliases: prefixes, suffixes, tokens, rules, and state-based rules. *)
  Module Export Coredefs.

    (** A [Prefix] is a [String] representing a matched prefix of the input. *)
    Definition Prefix : Type := String.
    (** A [Suffix] is a [String] representing the remaining unprocessed input. *)
    Definition Suffix : Type := String.
    (** A [Token] pairs a [Label] with the matched [Prefix]. *)
    Definition Token : Type := Label * Prefix.
    (** A [Rule] pairs a [Label] with the [regex] it recognizes. *)
    Definition Rule : Type := Label * regex.

    (** A state-based rule pairs a [Label] with a [State] (DFA node). *)
    Definition sRule : Type := Label * State.

    (** [eq_models fsm r] asserts that state [fsm] accepts exactly the strings matched by [r]. *)
    Inductive eq_models : State -> regex -> Prop :=
    | SReq (fsm : State) (r : regex)
           (H1 : forall(s : String), true = accepts s fsm <-> exp_match s r) :
        eq_models fsm r.

  End Coredefs.

  (** Inductive specifications for maximal-munch prefix matching and tokenization. *)
  Module Export MaxMunchSpec.

    (** [is_prefix p s] holds when [p] is a prefix of [s]. *)
    Inductive is_prefix : String -> String -> Prop :=
    | pref_def p s
               (H1 : exists q, p ++ q = s) :
        is_prefix p s.

    Notation "p ++_= s" := (is_prefix p s) (at level 80).

    (** [re_no_max_pref s r] holds when no prefix of [s] is matched by [r]. *)
    Inductive re_no_max_pref : String -> regex -> Prop :=
    | re_MP0 (s : String) (r : regex)
             (H1 : forall cand, cand ++_= s -> ~(exp_match cand r)) :
        re_no_max_pref s r.

    (** [re_max_pref s r p] holds when [p] is the longest prefix of [s] matched by [r]. *)
    Inductive re_max_pref : String -> regex -> String -> Prop :=
    | re_MP1 (s p : String) (r : regex)
             (H1 : p ++_= s)
             (H2 : exp_match p r)
             (H3 : forall(cand : String),
                 cand ++_= s
                 -> ((length cand) <= (length p)) \/ ~(exp_match cand r)) :
        re_max_pref s r p.

    (** [no_max_pref s fsm] holds when no prefix of [s] is accepted by [fsm]. *)
    Inductive no_max_pref : String -> State -> Prop :=
    | MP0 (s : String) (fsm : State)
          (H1 : exists(r : regex), eq_models fsm r /\ re_no_max_pref s r) :
        no_max_pref s fsm.

    (** [max_pref s fsm p] holds when [p] is the longest prefix of [s] accepted by [fsm]. *)
    Inductive max_pref : String -> State -> String -> Prop :=
    | MP1 (s p : String) (fsm : State)
          (H1 : exists(r : regex), eq_models fsm r /\ re_max_pref s r p) :
        max_pref s fsm p.

    (* a rule is at index 0 if it's the first element of the list.
   Otherwise a rule is at index n + 1 if it's at index n of the tail of the list *)
    (** [at_index ru n rus] holds when rule [ru] appears at position [n] in [rus]. *)
    Inductive at_index : Rule -> nat -> list Rule -> Prop :=
    | AI0 (ru h: Rule) (tl : list Rule)
          (Heq : ru = h) :
        at_index ru 0 (h :: tl)
    | AI1 (ru h: Rule) (n : nat) (tl : list Rule)
          (IH : at_index ru n tl) :
        at_index ru (S n) (h :: tl).

    (* n is the first index of a rule if no smaller index maps to that rule *)
    (** [least_index ru n rus] holds when [n] is the smallest index of [ru] in [rus]. *)
    Inductive least_index : Rule -> nat -> list Rule -> Prop :=
    | LI1 (ru : Rule) (n : nat) (rus : list Rule)
          (Hat : at_index ru n rus)
          (Hnot : forall(n' : nat), n' < n -> ~(at_index ru n' rus)) :
        least_index ru n rus.

    (* A rule is "earlier" than another if its first occurrence comes before
   the first occurence of the other rule *)
    (** [earlier_rule ru1 ru2 rus] holds when [ru1] first appears before [ru2] in [rus]. *)
    Inductive earlier_rule : Rule -> Rule -> list Rule -> Prop :=
    | ERu1 (ru1 ru2 : Rule) (rus : list Rule)
           (H : forall(n1 n2 : nat),
               least_index ru1 n1 rus
               -> least_index ru2 n2 rus
               -> n1 < n2) :
        earlier_rule ru1 ru2 rus.

    (** [first_token code rus (l,p)] holds when [(l,p)] is the maximal-munch, earliest-rule token for [code]. *)
    Inductive first_token : String -> (list Rule) -> Token -> Prop :=
    (* l is Token.label, p is Token.value *)
    | FT1 (code : String) (p : Prefix) (l : Label) (r : regex) (rus : list Rule)
          (Hnempt : p <> [])
          (Hex : In (l, r) rus)
          (Hmpref : re_max_pref code r p)
          (* We can't produce longer prefixes from other rules *)
          (Hout : forall(l' : Label) (r' : regex) (p' : String),
              length p' > length p
              -> re_max_pref code r' p'
              -> ~(In (l',r') rus)
          )
          (* If we can produce the prefix in some other way,
           the rule used to do so most come later in the list *)
          (Hlater : forall(r' : regex) (l' : Label),
              earlier_rule (l',r') (l, r) rus
              -> In (l', r') rus
              -> ~(re_max_pref code r' p)
          ) :
        first_token code rus (l, p).

    (* This definition accounts for inputs that could not be entirely tokenized.
   The list of tokens must match some prefix and the unprocessed suffix
   must match s1 *)
    (** [tokenized rus code ts rest] holds when [ts] is the token sequence for the prefix of [code] leaving [rest] unprocessed. *)
    Inductive tokenized (rus : list Rule) : String -> list Token -> String -> Prop :=
    | Tkd0 (code : String)
           (H : forall(t : Token), first_token code rus t -> snd t = []) :
        (* If no tokens can be produced from the input,
       then the input is tokenized by the empty list
       of tokens and itself *)
        tokenized rus code [] code
    | Tkd1 (p : Prefix) (s0 s1 : Suffix) (ts : list Token) (l : Label)
           (* the first token matches the input *)
           (H0 : first_token (p ++ s0 ++ s1) rus (l,p))
           (* The rest of the tokens match the rest of the input *)
           (IH : tokenized rus (s0 ++ s1) ts s1) :
        tokenized rus (p ++ s0 ++ s1) ((l, p) :: ts) s1.

    (** [rules_is_function rus] asserts each label maps to at most one regex in [rus]. *)
    Definition rules_is_function (rus : list Rule) :=
      forall l r r', In (l, r) rus
                -> In (l, r') rus
                -> r = r'.
  End MaxMunchSpec.



  (** Derived lemmas relating [eq_models], [init_state], and max-pref predicates. *)
  Module Export Corollaries.

    (** Decidable equality on [Rule] pairs; by [Label_eq_dec] and [regex_dec]. *)
    Lemma ru_dec : forall (ru1 ru2 : Rule), {ru1 = ru2} + {ru1 <> ru2}.
    Proof.
      intros. destruct ru1. destruct ru2.
      destruct (Label_eq_dec l l0); destruct (regex_dec r r0); subst; auto;
        right; intros C; destruct n; inv C; auto.
    Qed.

    (** [accepting (init_state e) = true] iff [e] matches [[]]; via [accepts_matches] and [accepts_nil]. *)
    Lemma accepting_nilmatch : forall e,
        true = accepting (init_state e)
        <-> exp_match [] e.
    Proof.
      intros. split; intros.
      - rewrite accepts_nil in H. rewrite accepts_matches in H. auto.
      - rewrite accepts_nil. rewrite accepts_matches. auto.
    Qed.

    (** [init_state e] is an [eq_models] witness for [e]; by [accepts_matches]. *)
    Lemma inv_eq_model : forall(e : regex),
        eq_models (init_state e) e.
    Proof.
      intros fsm. apply SReq. intros s. rewrite accepts_matches. split; auto.
    Qed.

    (*
    Lemma inv_transition : forall cand a e,
        exp_match cand (init_state_inv (transition a (init_state e)))
        <-> exp_match (a :: cand) (init_state_inv (init_state e)).
    Proof.
      intros. repeat rewrite <- accepts_matches.
      repeat rewrite accepts_matches.
      rewrite invert_init_correct.
      rewrite accepts_transition.
      split; auto.
    Qed.*)

    (** [re_max_pref code (init_state_inv (init_state r)) p] iff [re_max_pref code r p]; via [invert_init_correct]. *)
    Lemma invert_init_correct_max : forall r p code,
        re_max_pref code (init_state_inv (init_state r)) p
        <-> re_max_pref code r p.
    Proof.
      split; intros; inv H.
      - rewrite invert_init_correct in H2. apply re_MP1; auto.
        intros. apply H3 in H. destruct H; auto.
        right. intros C. destruct H. rewrite invert_init_correct. auto.
      - apply re_MP1; auto.
        + rewrite invert_init_correct. auto.
        + intros. apply H3 in H. destruct H; auto.
          right. intros C. destruct H. rewrite invert_init_correct in *. auto.
    Qed.

    (** [re_no_max_pref code (init_state_inv (init_state r))] iff [re_no_max_pref code r]; via [invert_init_correct]. *)
    Lemma invert_init_correct_nomax : forall r code,
        re_no_max_pref code (init_state_inv (init_state r))
        <-> re_no_max_pref code r.
    Proof.
      split; intros;
        inv H; apply re_MP0; intros; apply H1 in H;
          intros C; destruct H; apply invert_init_correct; auto.
    Qed.

  End Corollaries.


End DefsFn.


(** Module type alias for [DefsFn R Ty]. *)
Module Type DefsT (R : Regex.T) (Ty : State R).
  Include DefsFn R Ty.
End DefsT.

(** Bundled module type grouping a regex module [R], a state machine [Ty], and derived definitions [Defs]. *)
Module Type T.
  Declare Module R : Regex.T.
  Declare Module Ty : State R.
  Declare Module Defs : DefsT R Ty.
  Export R.
  Export R.Ty.
  Export R.Defs.
  Export Ty.
  Export Defs.
End T.
