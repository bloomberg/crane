From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.
(** WIP: A `sigT` whose payload is a pair of a value and a function emits two
    contradictory `any_cast`s of the same pair, and the function result is left
    as `std::any` in a `uint64_t`-returning position. *)

Module SigtPairFnPayload.
Definition item := sigT (fun A : Type => (A * (A -> nat))%type).
Definition mk (A : Type) (a : A) (f : A -> nat) : item := existT _ A (a, f).
Definition items : list item := [mk nat 3 (fun n => n); mk bool true (fun b => if b then 1 else 0)].
Definition score (it : item) : nat := match it with existT _ _ (a, f) => f a end.
Definition go : nat := fold_left (fun acc it => acc + score it) items 0.
End SigtPairFnPayload.
Crane Extraction "sigt_pair_fn_payload" SigtPairFnPayload.
