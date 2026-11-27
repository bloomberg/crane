(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** How [interp_st] runs a program: [Ret], [bind] and one event at a time,
    and what [runST] returns. *)

From Stdlib Require Import
  Morphisms
  Setoid
.

From Paco Require Import paco.

From ITree Require Import
  Events.Exception
  Events.State
  Events.StateFacts
  ITree
  ITreeFacts
.

From Crane Require Import
  Monads.Error
  Monads.ITree
  Monads.STMonad
.

Import Monads.
Local Open Scope monad_scope.

Section InterpST.

  Context {V : nat -> Type} {E : Type -> Type} `{exceptE Err -< E}.
  Notation E' := (STEvent model_refs V +' E).

  Lemma interp_st_Ret {R} (r : R) (m : mem V) :
    interp_st _ (ITreeDefinition.Ret r : itree E' R) m ≅ Ret (m, r).
  Proof. apply interp_state_ret. Qed.

  Lemma interp_st_Ret_eutt {R} (r : R) (m : mem V) :
    interp_st _ (ITreeDefinition.Ret r : itree E' R) m ≈ Ret (m, r).
  Proof. rewrite interp_st_Ret. reflexivity. Qed.

  Lemma interp_st_bind {A B} (t : itree E' A) (k : A -> itree E' B) (m : mem V) :
    interp_st _ (ITree.bind t k) m
    ≅ ITree.bind (interp_st _ t m) (fun p => interp_st _ (k (snd p)) (fst p)).
  Proof. apply interp_state_bind. Qed.

  Lemma interp_st_trigger {R} (e : E' R) (m : mem V) :
    interp_st _ (ITree.trigger e) m ≈ handle_STEvent_leave_rest _ e m.
  Proof. apply interp_state_trigger. Qed.

  (** Run the head of a bind whose effect on the store is already known, and
      continue with the rest of the program in the resulting store. *)
  Lemma interp_st_bind_Ret_l {A B} (t : itree E' A) (k : A -> itree E' B)
    (m m' : mem V) (r : A) (rest : itree E (mem V * B)) :
    interp_st _ t m ≈ Ret (m', r) ->
    interp_st _ (k r) m' ≈ rest ->
    interp_st _ (ITree.bind t k) m ≈ rest.
  Proof.
    intros Ht Hk. rewrite interp_st_bind, Ht. setoid_rewrite bind_ret_l. exact Hk.
  Qed.

End InterpST.

Section RunST.

  Context {V : nat -> Type} {E : Type -> Type} `{exceptE Err -< E}.

  (** [runST] returns what the program returns, interpreted in the model
      from the empty store. *)
  Lemma runST_Ret {A} (f : forall R : STRefs, itree (STEvent R V +' E) A) (m : mem V) (r : A) :
    interp_st _ (f model_refs) (@HMap.empty _ _ _ (st_hmap V)) ≈ Ret (m, r) ->
    runST f ≈ Ret r.
  Proof.
    intros Hf. unfold runST.
    rewrite Hf. setoid_rewrite map_ret. reflexivity.
  Qed.

End RunST.
