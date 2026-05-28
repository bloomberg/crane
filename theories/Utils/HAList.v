From Stdlib Require Import Classes.EquivDec List.
From ExtLib Require Import Structures.Reducible.
From Crane Require Import Utils.HMap.

Import ListNotations.

Section HAList.
  Context (K : Type) (V : K -> Type).

  Definition halist := list {k : K & V k}.

  Context `{Eq : EqDec K eq}.

  Definition halist_remove (k : K) (m : halist) : halist :=
    List.filter (fun k_v => negb (proj1_sig (bool_of_sumbool (projT1 k_v == k)))) m.

  Definition halist_add (k : K) (v : V k) (m : halist) : halist :=
    existT _ k v :: halist_remove k m.

  Fixpoint halist_lookup (k : K) (l : halist) : option (V k) :=
    match l with
    | [] => None
    | (existT _ k' v :: l') =>
      match k' == k with
      | left e => Some (eq_rect k' V v k e)
      | right _ => halist_lookup k l'
      end
    end.

  Section fold.
    Context {T : Type} (f : forall (k : K), V k -> T -> T).

    Fixpoint fold_halist (acc : T) (map : halist) : T :=
      match map with
      | [] => acc
      | (existT _ k v :: m) => fold_halist (f k v acc) m
      end.
  End fold.

  Definition halist_union (m1 m2 : halist) : halist :=
    fold_halist halist_add m2 m1.

  #[global] Instance HMap_halist : HMap K V halist :=
  { empty  := nil
  ; add    := @halist_add
  ; remove := @halist_remove
  ; lookup := @halist_lookup
  ; union  := @halist_union
  }.

  Section proofs.
    Definition mapsto_halist (k : K) (v : V k) (m : halist) : Prop :=
      halist_lookup k m = Some v.

    Theorem mapsto_empty_halist : forall (k : K) (v : V k), ~ mapsto_halist k v empty.
    Proof.
      intros ?? H.
      inversion H.
    Qed.

    Theorem mapsto_lookup_halist : forall (k : K) (v : V k) (m : halist),
      lookup k m = Some v <-> mapsto_halist k v m.
    Proof.
      reflexivity.
    Qed.

    Theorem mapsto_remove_eq_halist : forall m k v, ~ mapsto_halist k v (halist_remove k m).
    Proof.
      intros m k v.
      unfold mapsto_halist.
      induction m.
      - apply mapsto_empty_halist.
      - destruct a. cbn.
        destruct (x == k); [apply IHm|].
        cbn.
        destruct (x == k); [|apply IHm].
        contradiction.
    Qed.

    Theorem mapsto_remove_neq_halist : forall m k k', k <> k' ->
      forall v', (mapsto_halist k' v' m <-> mapsto_halist k' v' (halist_remove k m)).
    Proof.
      intros ??? Hneq ?.
      unfold mapsto_halist.
      induction m.
      - reflexivity.
      - destruct a.
        cbn.
        destruct (x == k) as [Heqk | Hneqk].
        + cbn. rewrite <- IHm.
          revert v.
          rewrite Heqk.
          destruct (k == k') as [Heqk' | _]; [exfalso; apply Hneq, Heqk'|reflexivity].
        + cbn. destruct (x == k') as [? | ?]; [reflexivity|apply IHm].
    Qed.

    Theorem mapsto_add_eq_halist : forall m k v, mapsto_halist k v (halist_add k v m).
    Proof.
      intros.
      unfold mapsto_halist.
      cbn.
      destruct (k == k) as [Heq | Hneq].
      - rewrite <- Eqdep_dec.eq_rect_eq_dec; [reflexivity|assumption].
      - exfalso. apply Hneq. reflexivity.
    Qed.

    Theorem mapsto_add_neq_halist : forall m k v k', k <> k' ->
      forall v', (mapsto_halist k' v' m <-> mapsto_halist k' v' (halist_add k v m)).
    Proof.
      intros ???? Hneq ?.
      unfold mapsto_halist.
      cbn.
      destruct (k == k') as [Heq | _].
      - exfalso. apply Hneq, Heq.
      - apply mapsto_remove_neq_halist, Hneq.
    Qed.

    #[global] Instance HMapOk_halist : HMapOk HMap_halist :=
      {| mapsto := mapsto_halist
       ; mapsto_empty := mapsto_empty_halist
       ; mapsto_lookup := mapsto_lookup_halist
       ; mapsto_add_eq := mapsto_add_eq_halist
       ; mapsto_add_neq := mapsto_add_neq_halist
       ; mapsto_remove_eq := mapsto_remove_eq_halist
       ; mapsto_remove_neq := mapsto_remove_neq_halist
      |}.
    
  End proofs.

  #[global] Instance Foldable_halist : Foldable halist {k : K & V k} :=
    fun _ f => fold_halist (fun k v => f (existT _ k v)).

End HAList.