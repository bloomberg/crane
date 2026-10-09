(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Set Crane SharedVariant] and [Set Crane BoxedFields], with a field
    typed by a parameter: the alternative already lives in a shared block,
    so the field is held in it directly, not in a [crane::field] box of its
    own.  Values are built at a
    pair and at a list, copied into a list, and read back. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module SharedVariantParamField.

Inductive step (A B : Type) : Type :=
| Done : A -> step A B
| More : B -> step A B
| Both : A -> B -> step A B.

Arguments Done {A B} _.
Arguments More {A B} _.
Arguments Both {A B} _ _.

Definition weight {A B} (fa : A -> nat) (fb : B -> nat) (s : step A B) : nat :=
  match s with
  | Done a => fa a
  | More b => fb b
  | Both a b => fa a + fb b
  end.

Definition pair_sum (p : nat * nat) : nat := fst p + snd p.

Definition steps : list (step (nat * nat) (list nat)) :=
  [Done (1, 2); More [3; 4]; Both (5, 6) [7]].

(* The list copies every step: copies share the blocks. *)
Definition result : nat :=
  fold_left Nat.add (map (weight pair_sum (fun l => fold_left Nat.add l 0)) (steps ++ steps)) 0.

End SharedVariantParamField.

Set Crane SharedVariant.
Set Crane BoxedFields.
Crane Extraction "shared_variant_param_field" SharedVariantParamField.
