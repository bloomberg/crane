From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.

Module NestedConcatMap.

(** Mapping a partially applied [concat] over a triply nested list leaves
    the member template's argument undeducible. *)
Definition cube := list (list (list nat)).

Definition sample : cube := [ [[1;2];[3]]; []; [[4];[5;6];[]] ].

Definition flatten (c : cube) : list nat := concat (concat c).

Definition regroup (c : cube) : list (list nat) := map (@concat nat) c.

Definition total : nat :=
  fold_left Nat.add (flatten sample) 0
  + fold_left (fun a l => a + length l) (regroup sample) 0.

End NestedConcatMap.
Crane Extraction "nested_concat_map" NestedConcatMap.
