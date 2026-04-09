From Stdlib Require Import Nat List.
Import ListNotations.
From Crane Require Mapping.Std Mapping.NatIntStd.
Require Crane.Extraction.

Set Crane Loopify.

Module LoopifyCoindStream.

CoInductive stream (A : Type) : Type :=
| scons : A -> stream A -> stream A.
Arguments scons {A}.

Definition hd {A} (s : stream A) : A :=
  match s with scons x _ => x end.
Definition tl {A} (s : stream A) : stream A :=
  match s with scons _ xs => xs end.

Fixpoint take {A} (n : nat) (s : stream A) : list A :=
  match n with
  | 0 => nil
  | S n' => cons (hd s) (take n' (tl s))
  end.

CoFixpoint iterate {A} (f : A -> A) (x : A) : stream A :=
  scons x (iterate f (f x)).

CoFixpoint smap {A B} (f : A -> B) (s : stream A) : stream B :=
  scons (f (hd s)) (smap f (tl s)).

CoFixpoint zipWith {A B C} (f : A -> B -> C)
  (s1 : stream A) (s2 : stream B) : stream C :=
  scons (f (hd s1) (hd s2)) (zipWith f (tl s1) (tl s2)).

CoFixpoint unfold {A S : Type} (f : S -> A * S) (seed : S) : stream A :=
  let '(a, s') := f seed in
  scons a (unfold f s').

Definition nats : stream nat := iterate S 0.
Definition doubled : stream nat := smap (fun n => n * 2) nats.
Definition sum_stream : stream nat := zipWith Nat.add nats doubled.
Definition fibs : stream nat :=
  unfold (fun '(a, b) => (a, (b, a + b))) (0, 1).

Definition test_nats_5 := take 5 nats.
Definition test_doubled_5 := take 5 doubled.
Definition test_sum_5 := take 5 sum_stream.
Definition test_fibs_8 := take 8 fibs.

End LoopifyCoindStream.

Crane Extraction "loopify_coind_stream" LoopifyCoindStream.
