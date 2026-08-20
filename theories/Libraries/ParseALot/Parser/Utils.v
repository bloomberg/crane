(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import Ascii BinNat Bool Lia List PeanoNat Relations Relation_Operators String.
From Crane.Libraries.ParseALot.Parser Require Import Tactics.
Import ListNotations.

(* STANDARD LIBRARY-LIKE DEFINITIONS *)

Section all_equal.

  Variable A   : Type.
  Variable beq : A -> A -> bool.
  Variable beq_eq : forall (x x' : A), beq x x' = true <-> x = x'.
  
  (** Returns [true] iff every element of [xs] is equal to [x] according to [beq]. *)
  Definition all_equal (x : A) (xs : list A) : bool :=
    forallb (beq x) xs.

  (** Splitting [all_equal] over a cons: the head must equal [x'] and the tail must satisfy [all_equal]. *)
  Lemma all_equal_inv_cons :
    forall x' x xs,
      all_equal x' (x :: xs) = true
      -> x' = x /\ all_equal x' xs = true.
  Proof.
    intros x' x xs ha.
    unfold all_equal in ha; sis.
    apply andb_true_iff in ha; destruct ha as [hhd htl]; split; auto.
    apply beq_eq; auto.
  Qed.

  (** Any element of a list satisfying [all_equal sp] must itself equal [sp]. *)
  Lemma all_equal_in_tl :
    forall sp sp' sps,
      all_equal sp sps = true
      -> In sp' sps
      -> sp' = sp.
  Proof.
    intros sp sp' sps ha hi; induction sps as [| sp'' sps IH]; inv hi;
      apply all_equal_inv_cons in ha; destruct ha as [hhd htl]; auto.
  Qed.

  (** If [all_equal] fails, there exists a list member that differs from the reference element. *)
  Lemma all_equal_false_exists_diff_rhs :
    forall sp sps,
      all_equal sp sps = false
      -> exists sp',
        In sp' sps
        /\ sp' <> sp.
  Proof.
    intros sp sps ha.
    induction sps as [| sp' sps IH]; simpl in ha.
    - inv ha.
    - apply andb_false_iff in ha; destruct ha as [hh | ht].
      + exists sp'; split.
        * apply in_eq.
        * intros heq; symmetry in heq; apply beq_eq in heq; tc. 
      + apply IH in ht; destruct ht as [sp'' [hi hn]].
        exists sp''; split; auto.
        apply in_cons; auto.
  Qed.

End all_equal.

(** Dependent map: applies [f a h] to each element [a] of [l], threading membership proofs [h : In a l]. *)
Definition dmap {A B : Type} :
  forall (l : list A) (f : forall (x : A), In x l -> B), list B.
  refine(fix dmap (l : list A) (f : forall x, In x l -> B) :=
           match l as l' return l = l' -> _ with
           | []     => fun _ => []
           | h :: t => fun Heq => (f h _) :: (dmap t _)
           end eq_refl).
  - subst.
    apply in_eq.
  - subst; intros x Hin.
    apply f with (x := x).
    apply in_cons; auto.
Defined.

(** Every element of [dmap l f] was produced by [f] applied to some member of [l]. *)
Lemma dmap_in :
  forall (A B : Type)
         (l   : list A)
         (f   : forall a, In a l -> B)
         (b   : B)
         (bs  : list B),
    dmap l f = bs
    -> In b bs
    -> (exists a hi, In a l /\ f a hi = b).
Proof.
  intros A B l f b bs hd hi; subst.
  induction l as [| a l IH].
  - inv hi.
  - destruct hi as [hh | ht].
    + exists a; eexists; split; eauto.
      apply in_eq.
    + apply IH in ht; destruct ht as [a' [hi [hi' heq]]].
      exists a'; eexists; split.
      * apply in_cons; auto.
      * apply heq.
Qed.

(** The maximum of a list of natural numbers, or 0 for the empty list. *)
Definition list_max (xs : list nat) : nat :=
  fold_right max 0 xs.

(** Every member of a list is at most the list's maximum. *)
Lemma list_max_in_le :
  forall (x : nat) (ys : list nat),
    In x ys
    -> x <= list_max ys.
Proof.
  intros x ys Hin; induction ys as [| y ys IH]; simpl in *.
  - inv Hin.
  - destruct Hin as [Heq | Hin]; subst.
    + apply Nat.le_max_l.
    + apply IH in Hin.
      eapply Nat.le_trans; eauto.
      apply Nat.le_max_r.
Qed.

(** Maps a list of lists to the list of their lengths. *)
Definition lengths {A} (xss : list (list A)) : list nat :=
  List.map (fun xs => List.length xs) xss.

(** Membership in [xss] implies membership of the corresponding length in [lengths xss]. *)
Lemma in__in_lengths :
  forall {A} (xs : list A) xss,
    In xs xss
    -> In (List.length xs) (lengths xss).
Proof.
  intros A xs xss hi; induction xss; simpl in *; inv hi; auto. 
Qed.

(** The length of the longest list in [xss], or 0 if [xss] is empty. *)
Definition max_length {A} (xss : list (list A)) : nat :=
  list_max (lengths xss).

(** Any member list of [xss] has length at most [max_length xss]. *)
Lemma mem_length_le_max :
  forall {A : Type} (xs : list A) (xss : list (list A)),
    In xs xss
    -> List.length xs <= max_length xss.
Proof.
  intros; unfold max_length.
  apply list_max_in_le.
  apply in__in_lengths; auto.
Qed.

(** Strict version of [mem_length_le_max]: [length xs < 1 + max_length xss], useful for the push termination bound. *)
Lemma mem_length_lt_max_plus_1 :
  forall A (xs : list A) xss,
    In xs xss
    -> List.length xs < 1 + max_length xss.
Proof.
  intros A xs xss hi.
  apply mem_length_le_max in hi; lia.
Qed.

(* Lemmas about standard library definitions *)

(** Symmetric form of [app_nil_r]: [xs = xs ++ []], useful for rewriting left-to-right. *)
Lemma app_nil_r' : forall A (xs : list A), xs = xs ++ [].
Proof.
  intros; rewrite app_nil_r; auto.
Qed.

(** Rewrites [xs] to [xs ++ []] in the goal, exposing a trailing nil for append lemmas. *)
Ltac rew_nil_r xs :=
  let heq := fresh "heq" in
  assert (heq : xs = xs ++ []) by apply app_nil_r'; rewrite heq; clear heq.

(** A cons is the same as appending a singleton: [x :: ys = [x] ++ ys]. *)
Lemma cons_app_singleton :
  forall A (x : A) (ys : list A),
    x :: ys = [x] ++ ys.
Proof.
  auto.
Qed.

(** Injectivity of cons: equal cons cells have equal heads and equal tails. *)
Lemma cons_inv_eq :
  forall A (x x' : A) (xs xs' : list A),
    x :: xs = x' :: xs'
    -> x' = x /\ xs' = xs.
Proof.
  intros A x x' xs xs' heq.
  inv heq; auto.
Qed.

(** If filtering produces a non-empty list, its head is a member of the original list. *)
Lemma filter_cons_in :
  forall (A : Type) (f : A -> bool) (l : list A) (hd : A) (tl : list A),
    filter f l = hd :: tl
    -> In hd l.
Proof.
  intros A f l hd tl Hf.
  assert (Hin : In hd (hd :: tl)) by apply in_eq.
  rewrite <- Hf in Hin.
  apply filter_In in Hin; destruct Hin as [Hp _]; auto.
Qed.

(** Any element in the tail of a filtered list is a member of the original list. *)
Lemma filter_tail_in :
  forall (A : Type) (f : A -> bool) (l : list A) (h x : A) (t : list A) ,
    filter f l = h :: t
    -> In x t
    -> In x l.
Proof.
  intros A f l h x t hf hi.
  assert (hi' : In x (filter f l)).
  { rewrite hf; apply in_cons; auto. }
  apply filter_In in hi'; destruct hi'; auto.
Qed.

(** The only member of a singleton list is the element itself. *)
Lemma in_singleton_eq :
  forall A (x x' : A),
    In x' [x]
    -> x' = x.
Proof.
  intros A x x' Hin.
  destruct Hin as [Hhd | Htl]; auto.
  inv Htl.
Qed.

(** Extracts the predicate [P x] from a [Forall P xs] witness and a membership proof. *)
Lemma forall_in :
  forall (A : Type) (P : A -> Prop) (x : A) (xs : list A),
    Forall P xs -> In x xs -> P x.
Proof.
  intros A P x xs hf hi.
  eapply Forall_forall; eauto.
Qed.    
         
(** If prepending [xs] to [ys] yields [ys], then [xs] must be empty. *)
Lemma app_left_identity_nil :
  forall A (xs ys : list A),
    xs ++ ys = ys
    -> xs = [].
Proof.
  intros A xs ys heq.
  eapply app_inv_tail.
  rewrite <- app_nil_l in heq; eauto.
Qed.

(** If prepending [xs] and [ys] to [zs] yields [zs], both [xs] and [ys] must be empty. *)
Lemma app_double_left_identity_nil :
  forall A (xs ys zs : list A),
    xs ++ ys ++ zs = zs
    -> xs = [] /\ ys = [].
Proof.
  intros A xs ys zs heq.
  apply app_eq_nil.
  eapply app_left_identity_nil; rewrite <- app_assoc; eauto.
Qed.

(** A list is never equal to its own tail: [x :: xs ≠ xs]. *)
Lemma cons_neq_tail :
  forall A x (xs : list A),
    (x :: xs) <> xs.
Proof.
  intros A x xs; unfold not; intros heq.
  assert (heq' : [x] ++ xs = [] ++ xs) by apps.
  apply app_inv_tail in heq'; inv heq'.
Qed.

(* Variant of filter_In that removes the conjunction *)
(** Convenience wrapper for [filter_In]: membership plus [f x = true] implies membership in the filtered list. *)
Lemma filter_in' :
  forall A (f : A -> bool) x l,
    In x l
    -> f x = true
    -> In x (filter f l).
Proof.
  intros; apply filter_In; auto.
Qed.

(** Regrouping: moves the middle element [y] into the left append, enabling left-to-right rewriting. *)
Lemma app_cons_group_l :
  forall A (xs zs : list A) (y : A),
    xs ++ y :: zs = (xs ++ [y]) ++ zs.
Proof.
  intros A xs zs y; rewrite <- app_assoc; auto.
Qed.

(** Groups the first and last elements of the left portion together, collecting both endpoints. *)
Lemma app_group_endpoints_l :
  forall A (x y : A) (xs ys : list A),
    x :: xs ++ y :: ys = (x :: xs ++ [y]) ++ ys.
Proof.
  intros A x y xs ys; simpl; apps.
Qed.

(* Get the bottom element of a stack, where stack ::= A * list A *)
(** Auxiliary fixpoint: returns the last element of [h :: t] by recursing to the end of [t]. *)
Fixpoint bottom_elt' {A} (h : A) (t : list A) : A :=
  match t with
  | []        => h
  | h' :: t' => bottom_elt' h' t'
  end.

(** Returns the bottom element of a non-empty stack represented as a head-tail pair. *)
Definition bottom_elt {A} (stk : A * list A) : A :=
  let (h, t) := stk in bottom_elt' h t.


(** Pairs a single source [s] with each element of [ds], producing a list of [(s, d)] pairs. *)
Definition one_to_many {A B : Type} (s : A) (ds : list B) : list (A * B) :=
  map (pair s) ds.

(** All pairs produced by [one_to_many a' bs] share the same source [a']. *)
Lemma one_to_many_src_eq :
  forall A B (a a' : A) (b : B) (bs : list B),
    In (a, b) (one_to_many a' bs)
    -> a' = a.
Proof.
  intros A B a a' b bs hi.
  apply in_map_iff in hi. destruct hi as [b' [heq hi]]; inv heq; auto.
Qed.

(** The destination component of any pair in [one_to_many a' bs] is a member of [bs]. *)
Lemma one_to_many_dst_in :
  forall A B (a a' : A) (b : B) (bs : list B),
    In (a, b) (one_to_many a' bs)
    -> In b bs.
Proof.
  intros A B a a' b bs hi.
  apply in_map_iff in hi; destruct hi as [? [heq ?]]; inv heq; auto.
Qed.

(* idea : use this for closure_step / closure_multistep *)
(** A transitive step followed by reflexive-transitive steps yields a transitive chain. *)
Lemma clos_t_rt :
  forall (A : Type) (R : relation A) (x y z : A),
    clos_trans A R x y
    -> clos_refl_trans A R y z
    -> clos_trans A R x z.
Proof.
  intros A R x y z ht hr.
  induction hr; eauto.
  eapply t_trans; eauto.
  apply t_step; auto.
Qed.


(** If [flat_map f xs] is empty, then [f] maps every element of [xs] to the empty list. *)
Lemma flat_map_nil__f_nil :
  forall X Y (f : X -> list Y) xs x,
    flat_map f xs = []
    -> In x xs
    -> f x = [].
Proof.
  intros X Y f xs x hf hi; induction xs as [| x' xs IH]; sis.
  - inv hi.
  - destruct hi; subst; apply app_eq_nil in hf; destruct hf; auto.
Qed.    

(** If [filter f xs] is empty, then [f] returns [false] on every element of [xs]. *)
Lemma filter_nil__f_false :
  forall X (f : X -> bool) (x : X) (xs : list X),
    filter f xs = []
    -> In x xs
    -> f x = false.
Proof.
  intros X f x xs hf hi.
  induction xs as [| x' xs IH]; sis.
  - inv hi.
  - destruct hi as [hh | ht]; subst; dm; auto; inv hf.
Qed.

(** Unfolds one step of [fold_right]: [fold_right f y (x :: xs) = f x (fold_right f y xs)]. *)
Lemma fold_right_unroll :
  forall X Y (f : X -> Y -> Y) (y : Y) (x : X) (xs : list X),
    fold_right f y (x :: xs) = f x (fold_right f y xs).
Proof.
  auto.
Qed.

(** Converts a list of types into a right-nested product type: [[A; B; C]] becomes [A * (B * (C * unit))]. *)
Fixpoint tuple (xs : list Type) : Type :=
  match xs with
  | [] => unit
  | x :: xs' => prod x (tuple xs')
  end.

  (** If [P] holds on [a] paired with prefix [xs], and [P] is stable under one fold step, then [P] holds after folding all of [ys] over the combined list [xs ++ ys]. *)
  Lemma fold_left_preserves_list_invar' :
    forall (A B   : Type)
           (f     : A -> B -> A)
           (xs ys : list B)
           (a     : A)
           (P     : A -> list B -> Prop),
      P a xs
      -> (forall a b bs, P a bs -> P (f a b) (bs ++ [b]))
      -> P (fold_left f ys a) (xs ++ ys).
  Proof.
    intros A B f xs ys; revert xs. 
    induction ys as [| y ys IH]; intros xs a P ha hf; sis.
    - rew_anr; auto.
    - apply hf with (b := y) in ha.
      apply IH with (xs := xs ++ [y]) in ha; auto.
      rewrite cons_app_singleton; apps.
  Qed.

  (** Specialisation of [fold_left_preserves_list_invar'] starting from an empty prefix: if [P a []] holds and [P] is stable, then [P (fold_left f bs a) bs]. *)
  Lemma fold_left_preserves_list_invar :
    forall (A B : Type)
           (f   : A -> B -> A)
           (bs  : list B)
           (a   : A)
           (P   : A -> list B -> Prop),
      P a []
      -> (forall a b bs, P a bs -> P (f a b) (bs ++ [b]))
      -> P (fold_left f bs a) bs.
  Proof.
    intros.
    rewrite <- app_nil_l.
    apply fold_left_preserves_list_invar'; auto.
  Qed.

  (** Lifts a membership witness from [xs] to the appended list [xs ++ ys]. *)
  Lemma exists_in_app_l :
    forall (A     : Type)
           (xs ys : list A),
      (exists x, In x xs)
      -> exists x, In x (xs ++ ys).
  Proof.
    intros A xs ys [x Hi].
    eexists; apply in_or_app; left; eauto.
  Qed.

  (** Two cons cells are equal iff their heads are equal and their tails are equal. *)
  Lemma heads_eq_tails_eq__lists_eq :
    forall (A : Type) (x y : A) (xs ys : list A),
      (x = y /\ xs = ys) <-> x :: xs = y :: ys.
  Proof.
    intros A x y xs ys; split; [intros [h h'] | intros h]; subst; auto.
    inv h; auto.
  Qed.

  (** Relates snoc ([xs ++ [x]]) to a reverse-based form, used to reason about reversed lists. *)
  Lemma rev_cons_rev_eq_app :
    forall A (x : A) (xs : list A),
      xs ++ [x] = rev (x :: (rev xs)).
  Proof.
    intros A x xs.
    rewrite <- rev_unit.
    rewrite rev_involutive; auto.
  Qed.
  
  (** Two snoc lists are equal iff their last elements are equal and their prefixes are equal. *)
  Lemma rev_heads_eq_tails_eq__lists_eq :
    forall (A : Type) (x y : A) (xs ys : list A),
      (x = y /\ xs = ys) <-> xs ++ [x] = ys ++ [y].
  Proof.
    intros A x y xs ys; split; [intros [h h'] | intros h]; subst; auto.
    repeat rewrite rev_cons_rev_eq_app in h.
    apply List.rev_inj in h.
    apply heads_eq_tails_eq__lists_eq in h.
    destruct h as [? h]; subst.
    apply List.rev_inj in h; auto.
  Qed.

  (** Constructs pair equality from component equalities: [a = a' -> b = b' -> (a, b) = (a', b')]. *)
  Lemma pair_split_eq :
    forall A B (a a' : A) (b b' : B),
      a = a' -> b = b' -> (a, b) = (a', b').
  Proof.
    intros A B a a' b b' ? ?; subst; auto.
  Qed.

  (** Destructs a hypothesis of the form [(a, b) = (a', b')] into component equalities. *)
  Ltac inv_pr_eq :=
    match goal with
    | H : (_, _) = (_, _) |- _ =>
      inv H
    end.

