(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Heterogeneous association lists, [list {k : K & V k}]: an [HMap]
    instance with its [HMapOk] proof ([hmap_ok_halist]) and a [Foldable]
    instance. *)
From Stdlib Require Import Classes.EquivDec List.
From ExtLib Require Import Structures.Reducible.
From Crane Require Import Utils.HMap.

Import ListNotations.

Section HAList.
  Context (K : Type) (V : K -> Type).

  (** A dependent association list; [halist_add] keeps keys unique, and
      [halist_lookup] reads the first binding. *)
  Definition halist := list {k : K & V k}.

  Context `{Eq : EqDec K eq}.

  (** Drop every binding of [k]. *)
  Definition halist_remove (k : K) (m : halist) : halist :=
    List.filter (fun k_v => negb (proj1_sig (bool_of_sumbool (projT1 k_v == k)))) m.

  (** Bind [k] to [v] at the front, replacing any old binding. *)
  Definition halist_add (k : K) (v : V k) (m : halist) : halist :=
    existT _ k v :: halist_remove k m.

  (** The first binding of [k], its value cast to [V k] along the decided
      key equality. *)
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

    (** Fold [f] over the bindings, front to back. *)
    Fixpoint fold_halist (acc : T) (map : halist) : T :=
      match map with
      | [] => acc
      | (existT _ k v :: m) => fold_halist (f k v acc) m
      end.
  End fold.

  (** Union; [m1]'s bindings win, being added over [m2]. *)
  Definition halist_union (m1 m2 : halist) : halist :=
    fold_halist halist_add m2 m1.

  (** Association lists are an [HMap]. *)
  #[global] Instance HMap_halist : HMap K V halist :=
  { empty  := nil
  ; add    := @halist_add
  ; remove := @halist_remove
  ; lookup := @halist_lookup
  ; union  := @halist_union
  }.

  Section proofs.
    (** [k] maps to [v] when lookup finds exactly [v]. *)
    Definition mapsto_halist (k : K) (v : V k) (m : halist) : Prop :=
      halist_lookup k m = Some v.

    (** The empty list binds nothing. *)
    Theorem mapsto_empty_halist : forall (k : K) (v : V k), ~ mapsto_halist k v empty.
    Proof.
      intros ?? H.
      inversion H.
    Qed.

    (** [lookup] and [mapsto_halist] agree by definition. *)
    Theorem mapsto_lookup_halist : forall (k : K) (v : V k) (m : halist),
      lookup k m = Some v <-> mapsto_halist k v m.
    Proof.
      reflexivity.
    Qed.

    (** A removed key is unbound. *)
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

    (** Removing [k] leaves every other key's binding alone. *)
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

    (** An added key maps to its new value. *)
    Theorem mapsto_add_eq_halist : forall m k v, mapsto_halist k v (halist_add k v m).
    Proof.
      intros.
      unfold mapsto_halist.
      cbn.
      destruct (k == k) as [Heq | Hneq].
      - rewrite <- Eqdep_dec.eq_rect_eq_dec; [reflexivity|assumption].
      - exfalso. apply Hneq. reflexivity.
    Qed.

    (** Adding [k] leaves every other key's binding alone. *)
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

    (** Association lists meet the [HMapOk] specification. *)
    #[global] Instance hmap_ok_halist : HMapOk HMap_halist :=
      {| mapsto := mapsto_halist
       ; mapsto_empty := mapsto_empty_halist
       ; mapsto_lookup := mapsto_lookup_halist
       ; mapsto_add_eq := mapsto_add_eq_halist
       ; mapsto_add_neq := mapsto_add_neq_halist
       ; mapsto_remove_eq := mapsto_remove_eq_halist
       ; mapsto_remove_neq := mapsto_remove_neq_halist
      |}.
    
  End proofs.

  (** Fold over the bindings as dependent pairs, front to back. *)
  #[global] Instance Foldable_halist : Foldable halist {k : K & V k} :=
    fun _ f => fold_halist (fun k v => f (existT _ k v)).

End HAList.