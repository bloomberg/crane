(** A carrier written inside another carrier's body.

    [stateT nat (stateT bool (itree noE))] is written through two
    synthesised alias templates: one for [itree noE], and one for
    [stateT bool (itree noE)], whose body names the first.  The inner one is
    written nowhere else, so it is found only by spelling the outer one's
    body.  Its body names the module's own [noE], so it is declared inside
    the module's struct, under the name the outer body spells, ahead of the
    outer one -- not in front of the struct, where [noE] is undeclared. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.

Module NestedCarrierAlias.
  Definition stateT (S : Type) (M : Type -> Type) (A : Type) : Type := S -> M (prod S A).

  Variant noE : Type -> Type := .

  Definition stacked_id (m : stateT nat (stateT bool (itree noE)) nat)
    : stateT nat (stateT bool (itree noE)) nat := m.

  Definition five : nat := 5.
End NestedCarrierAlias.

Crane Extraction "nested_carrier_alias" NestedCarrierAlias.
