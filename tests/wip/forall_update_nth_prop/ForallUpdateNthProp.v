(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: Forall-bound nibble lists remain bounded after update_nth. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module ForallUpdateNthProp.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Definition sample : list nat := [1; 2; 3; 4].
Definition t : Prop :=
  Forall (fun x => x < 16) sample /\
  9 < 16 /\
  Forall (fun x => x < 16) (update_nth 1 9 sample).

End ForallUpdateNthProp.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "forall_update_nth_prop" ForallUpdateNthProp.
