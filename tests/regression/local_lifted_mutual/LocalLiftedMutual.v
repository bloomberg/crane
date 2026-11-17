From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** A local mutual group used at two types has type variables of its own,
    so it is lifted out of [run] to function templates.  Every member was
    lifted under the name of the member the group is projected to, and a
    member's references to its partners were left as they were: [f] called
    an undeclared [g].  Each member is lifted to a helper of its own, and
    reaches its partners as it reaches itself.  A partner passed a closure
    that flows back is [local_lifted_mutual_closure_back]. *)

Module LocalLiftedMutual.

  Definition run (k : nat) (n : nat) : nat :=
    let fp := fix f (A : Type) (h : A -> nat) (y : A) (n : nat) : nat :=
      match n with
      | O => h y
      | S m => g A h y m + 1
      end
    with g (A : Type) (h : A -> nat) (x : A) (n : nat) : nat :=
      match n with
      | O => h x + k
      | S m => f A h x m
      end
    for f in
    fp (list nat) (@length nat) [1; 2; 3] n + fp bool (fun b => if b then 1 else 2) true n.

End LocalLiftedMutual.

Crane Extraction "local_lifted_mutual" LocalLiftedMutual.
