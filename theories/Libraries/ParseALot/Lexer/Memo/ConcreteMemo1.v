(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.

From Stdlib Require Import FSets FSets.FMapAVL FSets.FMapFacts.
From Stdlib Require Import Lia.

From Crane.Libraries.ParseALot.Lexer Require Import State.
From Crane.Libraries.ParseALot.Lexer.Memo Require Import Memo.
From Crane.Libraries.ParseALot.Utils Require Import Ltac.
From Crane.Libraries.ParseALot.Utils Require Import Orders.
From Crane.Libraries.ParseALot.Utils Require Import Tape.


(** Concrete tape-backed memo table satisfying the [Memo] interface.
    Each tape cell at position [index2nat i] holds a finite map from
    [Pointer] to cached prefixing results. *)
Module FMemo (STT : State.T) <: Memo STT.

  Import STT.Ty.
  Import STT.Defs.
  Import STT.R.Defs.

  Module Pointer_as_UOT <: UsualOrderedType := UOT_from_UCT Pointer_as_UCT.
  Module FM := FMapAVL.Make Pointer_as_UOT.
  Module FMF := FMapFacts.Facts FM.

  (** Injectively map a list of booleans to a natural number.
      Empty list maps to 0; [false :: rest] maps to an odd positive number;
      [true :: rest] maps to an even positive number. *)
  Fixpoint list_bool_to_nat (l : list bool) : nat :=
    match l with
    | []           => 0
    | false :: rest => S (2 * list_bool_to_nat rest)
    | true  :: rest => S (S (2 * list_bool_to_nat rest))
    end.

  (** [list_bool_to_nat] is injective. *)
  Lemma list_bool_to_nat_inj : forall l1 l2,
      list_bool_to_nat l1 = list_bool_to_nat l2 -> l1 = l2.
  Proof.
    induction l1 as [|[] l1 IH]; destruct l2 as [|[] l2]; intro H; simpl in H;
      try reflexivity; try discriminate; try lia.
    - f_equal. apply IH. lia.
    - f_equal. apply IH. lia.
  Qed.

  (** Convert an index to a natural number via its list-of-bools encoding. *)
  Definition index2nat (i : index) : nat := list_bool_to_nat (index2list i).

  (** [index2nat] is injective. *)
  Lemma index2nat_inj : forall i i',
      index2nat i = index2nat i' -> i = i'.
  Proof.
    unfold index2nat. intros i i' Heq.
    apply list_bool_to_nat_inj in Heq.
    apply f_equal with (f := list2index) in Heq.
    repeat rewrite list_inv in Heq. exact Heq.
  Qed.

  (** A memo table maps each index position to a finite map from pointers to cached results. *)
  Definition Memo : Type := @tape (FM.t (option (String * String * index))).
  (** The empty memo table. *)
  Definition emptyMemo : Memo := empty_tape.

  (** Look up the cached result for [(pnt, i)] in memo [M]; returns [None] if absent. *)
  Definition get_Memo (M : Memo) (pnt : Pointer) (i : index)
    : option (option (String * String * index)) :=
    match get_tape (index2nat i) M with
    | None    => None
    | Some MP => FM.find pnt MP
    end.

  (** Store result [o] for key [(pnt, i)] into memo [M]. *)
  Definition set_Memo (M : Memo) (pnt : Pointer) (i : index)
             (o : (option (String * String * index))) : Memo :=
    match get_tape (index2nat i) M with
    | None    => set_tape (FM.add pnt o (@FM.empty (option (String * String * index))))
                          (index2nat i) M
    | Some MP => set_tape (FM.add pnt o MP) (index2nat i) M
    end.

  (** Reading back the just-written key always returns [Some o]. *)
  Lemma correct_Memo : forall M ptr i o, get_Memo (set_Memo M ptr i o) ptr i = Some o.
  Proof.
    intros. unfold get_Memo, set_Memo. repeat dm.
    - rewrite get_of_set_eq in E; repeat inj_all. apply FMF.add_eq_o; auto.
    - rewrite get_of_set_eq in E; repeat inj_all. apply FMF.add_eq_o; auto.
    - rewrite get_of_set_eq in E; discriminate.
    - rewrite get_of_set_eq in E; discriminate.
  Qed.

  (** Writing to a different key [(ptr', i')] does not affect lookup at [(ptr, i)]. *)
  Lemma correct_Memo_moot : forall M ptr ptr' i i' o,
      (ptr <> ptr' \/ i <> i')
      ->
      get_Memo (set_Memo M ptr' i' o) ptr i = get_Memo M ptr i.
  Proof.
    intros M ptr ptr' i i' o H. unfold get_Memo, set_Memo.
    destruct (index_eq_dec i i') as [<- | Hi].
    - (* i = i': the write hits the same tape cell; pointer must differ *)
      destruct H as [Hp | ?]; [| contradiction].
      destruct (get_tape (index2nat i) M) eqn:Eg.
      + rewrite get_of_set_eq. simpl.
        rewrite FMF.add_neq_o; [reflexivity | intro C; apply Hp; symmetry; exact C].
      + rewrite get_of_set_eq. simpl.
        rewrite FMF.add_neq_o; [apply FMF.empty_o | intro C; apply Hp; symmetry; exact C].
    - (* i ≠ i': the write hits a different tape cell; use get_of_set_neq *)
      assert (Hni : index2nat i' <> index2nat i) by
        (intro C; apply Hi; apply index2nat_inj; symmetry; exact C).
      destruct (get_tape (index2nat i') M) eqn:Eg;
        rewrite get_of_set_neq by exact Hni; reflexivity.
  Qed.

  (** The empty memo has no entries at any key. *)
  Lemma correct_emptyMemo : forall stt z, get_Memo emptyMemo stt z = None.
  Proof.
    intros. unfold get_Memo, emptyMemo. rewrite get_empty_tape. reflexivity.
  Qed.

End FMemo.


(** Packages [FMemo] together with its definitions into the [Memo.T] interface. *)
Module memoTFn (STT' : State.T) <: Memo.T.
  Module STT := STT'.
  Module MemTy <: Memo STT := FMemo STT.
  Module Defs := Memo.MemoDefsFn STT MemTy.
End memoTFn.
