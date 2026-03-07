(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: Forall-bound nibble lists remain bounded under firstn. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module ForallFirstnProp.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Definition sample : list nat := [1; 2; 3; 4].
Definition t : Prop :=
  Forall (fun x => x < 16) sample /\
  Forall (fun x => x < 16) (firstn 2 sample).

End ForallFirstnProp.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "forall_firstn_prop" ForallFirstnProp.
