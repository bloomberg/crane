(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Coinductive guardedness — cofold, zipWith, iterate. *)

From Stdlib Require Import Nat List.
Import ListNotations.

Module CoindGuard.

CoInductive Stream (A : Type) : Type :=
  | Cons : A -> Stream A -> Stream A.

Arguments Cons {A}.

Definition hd {A : Type} (s : Stream A) : A :=
  match s with Cons x _ => x end.

Definition tl {A : Type} (s : Stream A) : Stream A :=
  match s with Cons _ t => t end.

(* iterate f x = x, f x, f (f x), ... *)
CoFixpoint iterate {A : Type} (f : A -> A) (x : A) : Stream A :=
  Cons x (iterate f (f x)).

(* zipWith on two streams *)
CoFixpoint zipWith {A B C : Type} (f : A -> B -> C)
  (s1 : Stream A) (s2 : Stream B) : Stream C :=
  Cons (f (hd s1) (hd s2)) (zipWith f (tl s1) (tl s2)).

(* map on streams *)
CoFixpoint smap {A B : Type} (f : A -> B) (s : Stream A) : Stream B :=
  Cons (f (hd s)) (smap f (tl s)).

(* cofold: unfold a stream from a seed *)
CoFixpoint unfold {A S : Type} (f : S -> A * S) (seed : S) : Stream A :=
  let '(a, s') := f seed in
  Cons a (unfold f s').

(* take n elements *)
Fixpoint take {A : Type} (n : nat) (s : Stream A) : list A :=
  match n with
  | 0 => nil
  | S n' => cons (hd s) (take n' (tl s))
  end.

(* Test values *)
Definition nats : Stream nat := iterate S 0.
Definition evens : Stream nat := smap (fun n => n * 2) nats.
Definition fibs : Stream nat :=
  unfold (fun '(a, b) => (a, (b, a + b))) (0, 1).
Definition sum_stream : Stream nat := zipWith Nat.add nats evens.

Definition test_nats_5 : list nat := take 5 nats.
Definition test_evens_5 : list nat := take 5 evens.
Definition test_fibs_8 : list nat := take 8 fibs.
Definition test_sum_5 : list nat := take 5 sum_stream.
Definition test_iterate_hd : nat := hd nats.

End CoindGuard.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Crane Extraction "coind_guard" CoindGuard.
