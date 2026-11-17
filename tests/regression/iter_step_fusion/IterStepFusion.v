(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

(** An interaction-tree library in miniature, shaped as coq-itree's: [iter]
    binds each step's result, and [interp] supplies the step as a literal
    lambda.  Specializing [iter] to that lambda lets each passthrough step
    build its next node directly instead of a [Ret] for [bind] to take
    apart; [interp_by_name], whose step is a definition, is the same
    interpreter unspecialized. *)
Module IterStepFusion.

Variant itreeF (R itree : Type) : Type :=
| RetF (r : R)
| TauF (t : itree)
| VisF (e : nat) (k : nat -> itree).

CoInductive itree (R : Type) : Type := go { _observe : itreeF R (itree R) }.

Arguments go {R} _.
Arguments _observe {R} _.
Arguments RetF {R itree} r.
Arguments TauF {R itree} t.
Arguments VisF {R itree} e k.

Definition observe {R} (t : itree R) : itreeF R (itree R) := _observe t.
Definition Ret {R} (r : R) : itree R := go (RetF r).
Definition Tau {R} (t : itree R) : itree R := go (TauF t).
Definition Vis {R} (e : nat) (k : nat -> itree R) : itree R := go (VisF e k).

Definition subst {T U} (k : T -> itree U) : itree T -> itree U :=
  cofix _subst (u : itree T) : itree U :=
    match observe u with
    | RetF r => k r
    | TauF t => Tau (_subst t)
    | VisF e h => Vis e (fun x => _subst (h x))
    end.

Definition bind {T U} (u : itree T) (k : T -> itree U) : itree U := subst k u.

Definition iter {I R} (step : I -> itree (I + R)) : I -> itree R :=
  cofix iter_ i := bind (step i) (fun lr => match lr with
                                         | inl l => Tau (iter_ l)
                                         | inr r => Ret r
                                         end).

Definition fmap {A B} (f : A -> B) (t : itree A) : itree B := bind t (fun x => Ret (f x)).

(** Specialized: the step is a lambda. *)
Definition interp {R} (h : nat -> itree nat) : itree R -> itree R :=
  iter (fun t =>
    match observe t with
    | RetF r => Ret (inr r)
    | TauF t => Ret (inl t)
    | VisF e k => fmap (fun x => inl (k x)) (h e)
    end).

(** Not specialized: the same step, by name. *)
Definition step {R} (h : nat -> itree nat) (t : itree R) : itree (itree R + R) :=
  match observe t with
  | RetF r => Ret (inr r)
  | TauF t => Ret (inl t)
  | VisF e k => fmap (fun x => inl (k x)) (h e)
  end.

Definition interp_by_name {R} (h : nat -> itree nat) : itree R -> itree R :=
  iter (step h).

End IterStepFusion.

Crane Extraction "iter_step_fusion" IterStepFusion.
