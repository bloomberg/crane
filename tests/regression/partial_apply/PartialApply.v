(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Partial application of constructors — map S, map (pair 1), etc. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module PartialApply.

(* Partial application of S (successor) *)
Definition inc_all (l : list nat) : list nat := map S l.

(* Partial application of pair *)
Definition tag_all (l : list nat) : list (nat * nat) := map (pair 1) l.

(* Partial application of Some *)
Definition wrap_all (l : list nat) : list (option nat) := map Some l.

(* Partial application of cons *)
Definition prepend_each (l : list nat) : list (list nat -> list nat) := map cons l.

(* Partial application of user-defined constructor *)
Inductive tagged (A : Type) :=
  | Tag : nat -> A -> tagged A.

Definition tag_with (n : nat) (l : list bool) : list (tagged bool) := map (Tag bool n) l.

(* Nested partial application *)
Definition double_tag (l : list nat) : list (nat * (nat * nat)) :=
  map (fun x => (x, (x, x))) l.

(* Partial application in fold *)
Definition sum_with_init (init : nat) (l : list nat) : nat :=
  List.fold_left Nat.add l init.

(* === Test values === *)

Definition test_inc : list nat := inc_all [1; 2; 3].
Definition test_tag : list (nat * nat) := tag_all [10; 20; 30].
Definition test_wrap : list (option nat) := wrap_all [5; 6; 7].
Definition test_tag_with : list (tagged bool) := tag_with 99 [true; false; true].
Definition test_sum : nat := sum_with_init 100 [1; 2; 3].

End PartialApply.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "partial_apply" PartialApply.
