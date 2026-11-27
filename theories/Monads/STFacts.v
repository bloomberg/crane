(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** How [ST.interp] runs a program: [Ret], [bind] and one event at a time,
    and what [ST.run] returns. *)

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
  Monads.ST
.

Import Monads.
Local Open Scope monad_scope.

Section Interp.

  Context {V : nat -> Type} {E : Type -> Type} `{exceptE Err -< E}.
  Notation E' := (ST.Event ST.model_refs V +' E).

  Lemma interp_ret {R} (r : R) (m : mem V) :
    ST.interp _ (ITreeDefinition.Ret r : itree E' R) m ≅ Ret (m, r).
  Proof. apply interp_state_ret. Qed.

  Lemma interp_ret_eutt {R} (r : R) (m : mem V) :
    ST.interp _ (ITreeDefinition.Ret r : itree E' R) m ≈ Ret (m, r).
  Proof. rewrite interp_ret. reflexivity. Qed.

  Lemma interp_bind {A B} (t : itree E' A) (k : A -> itree E' B) (m : mem V) :
    ST.interp _ (ITree.bind t k) m
    ≅ ITree.bind (ST.interp _ t m) (fun p => ST.interp _ (k (snd p)) (fst p)).
  Proof. apply interp_state_bind. Qed.

  Lemma interp_trigger {R} (e : E' R) (m : mem V) :
    ST.interp _ (ITree.trigger e) m ≈ ST.handle_leave_rest _ e m.
  Proof. apply interp_state_trigger. Qed.

  (** Run the head of a bind whose effect on the store is already known, and
      continue with the rest of the program in the resulting store. *)
  Lemma interp_bind_ret_l {A B} (t : itree E' A) (k : A -> itree E' B)
    (m m' : mem V) (r : A) (rest : itree E (mem V * B)) :
    ST.interp _ t m ≈ Ret (m', r) ->
    ST.interp _ (k r) m' ≈ rest ->
    ST.interp _ (ITree.bind t k) m ≈ rest.
  Proof.
    intros Ht Hk. rewrite interp_bind, Ht. setoid_rewrite bind_ret_l. exact Hk.
  Qed.

End Interp.

Section Run.

  Context {V : nat -> Type} {E : Type -> Type} `{exceptE Err -< E}.

  (** [ST.run] returns what the program returns, interpreted in the model
      from the empty store. *)
  Lemma run_ret {A} (f : forall R : ST.Refs, itree (ST.Event R V +' E) A) (m : mem V) (r : A) :
    ST.interp _ (f ST.model_refs) (@HMap.empty _ _ _ (ST.hmap V)) ≈ Ret (m, r) ->
    ST.run f ≈ Ret r.
  Proof.
    intros Hf. unfold ST.run.
    rewrite Hf. setoid_rewrite map_ret. reflexivity.
  Qed.

End Run.
