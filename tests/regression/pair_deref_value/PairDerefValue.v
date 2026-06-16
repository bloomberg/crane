(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** WIP test: Crane emits spurious dereference in functor-generated code
    when destructuring a pair whose second element is a recursive type. *)
From Stdlib Require Import List.
Import ListNotations.
Require Crane.Extraction.
From Crane Require Import Mapping.Std.

(* A module type providing a key type *)
Module Type HasKey.
  Parameter key : Type.
  Parameter key_eq_dec : forall (x y : key), {x = y} + {x <> y}.
End HasKey.

(* A functor that pattern-matches list of (key * list key) pairs *)
Module Collector (K : HasKey).

  Definition production := (K.key * list K.key)%type.

  Fixpoint rhss_for (ps : list production) (x : K.key) : list (list K.key) :=
    match ps with
    | [] => []
    | (x', gamma) :: ps' =>
      if K.key_eq_dec x' x then
        gamma :: rhss_for ps' x
      else
        rhss_for ps' x
    end.

End Collector.

(* Instantiate with nat as key *)
Module NatKey <: HasKey.
  Definition key := nat.
  Lemma key_eq_dec : forall (x y : nat), {x = y} + {x <> y}.
  Proof. decide equality. Qed.
End NatKey.

Module C := Collector NatKey.

Definition test_prods : list C.production := [(1, [10;20]); (2, [30]); (1, [40])].
Definition test_result : list (list nat) := C.rhss_for test_prods 1.

Set Crane Loopify.
Crane Separate Extraction test_result.
