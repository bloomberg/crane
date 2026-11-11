(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Inductives whose parameter context has let-in parameters.  A let-in
    parameter binds a de Bruijn index in the constructors' types like any
    other, but is not a parameter the inductive is applied to, so the type
    variables of the fields after it are found by de Bruijn level over all
    the parameter declarations, let-ins included. *)

From Stdlib Require Import List.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Import ListNotations.

Module InductiveLetinParams.

(** A let-in between two type parameters, used by a field. *)
Inductive tri (A : Type) (L := list A) (B : Type) : Type :=
| Tri : A -> B -> L -> tri A B.

Arguments Tri {A B} _ _ _.

Definition tri_first {A B} (t : tri A B) : A := match t with Tri a _ _ => a end.
Definition tri_second {A B} (t : tri A B) : B := match t with Tri _ b _ => b end.
Definition tri_rest {A B} (t : tri A B) : list A := match t with Tri _ _ l => l end.

Definition sample : tri nat bool := Tri 7 true [1; 2; 3].

Definition sample_sum : nat := fold_left Nat.add (tri_rest sample) (tri_first sample).

(** A let-in after the type parameters, in a recursive inductive. *)
Inductive tagged (A B : Type) (P := (A * B)%type) : Type :=
| Tnil : tagged A B
| Tcons : P -> tagged A B -> tagged A B.

Arguments Tnil {A B}.
Arguments Tcons {A B} _ _.

Fixpoint tagged_firsts {A B} (t : tagged A B) : list A :=
  match t with
  | Tnil => []
  | Tcons p rest => fst p :: tagged_firsts rest
  end.

Fixpoint tagged_seconds {A B} (t : tagged A B) : list B :=
  match t with
  | Tnil => []
  | Tcons p rest => snd p :: tagged_seconds rest
  end.

Definition sample_tagged : tagged nat bool :=
  Tcons (1, true) (Tcons (2, false) Tnil).

(** A let-in parameter before an index the constructor binds: the field
    [x : T] reads its type through the binder of [T], found by de Bruijn
    level past the parameter context, the let-in counted. *)
Inductive wrap (k := 1) : Type -> Type :=
| Wrap : forall T : Type, T -> wrap T.

Definition unwrap {T} (w : wrap T) : T :=
  match w in wrap T' return T' with Wrap _ x => x end.

Definition sample_wrap : wrap nat := Wrap nat 5.

Definition unwrapped : nat := unwrap sample_wrap.

End InductiveLetinParams.

Crane Extraction "inductive_letin_params" InductiveLetinParams.
