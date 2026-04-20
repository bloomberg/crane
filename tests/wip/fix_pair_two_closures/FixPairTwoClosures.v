From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module FixPairTwoClosures.

(** Two local fixpoints escape through a pair.

    BUG: Both [f] and [g] use [&] capture. They capture [a], [b],
    and each other's [std::function] variables. All captured references
    dangle after [make_ops] returns. *)

Definition make_ops (a b : nat) : (nat -> nat) * (nat -> nat) :=
  let fix f (x : nat) : nat :=
    match x with
    | O => a
    | S x' => S (f x')
    end
  in
  let fix g (x : nat) : nat :=
    match x with
    | O => b
    | S x' => S (g x')
    end
  in (f, g).

(** test1: make_ops(10, 20). fst(3) = 10+3 = 13, snd(5) = 20+5 = 25.
    Total = 38. *)
Definition test1 : nat :=
  let '(f, g) := make_ops 10 20 in
  f 3 + g 5.

(** test2: Use both closures interleaved.
    fst(1) + snd(2) + fst(3) = 11 + 22 + 13 = 46. *)
Definition test2 : nat :=
  let '(f, g) := make_ops 10 20 in
  f 1 + g 2 + f 3.

(** test3: Asymmetric arguments to stress different captured values.
    make_ops(100, 1). fst(0) + snd(0) = 100 + 1 = 101. *)
Definition test3 : nat :=
  let '(f, g) := make_ops 100 1 in
  f 0 + g 0.

End FixPairTwoClosures.

Crane Extraction "fix_pair_two_closures" FixPairTwoClosures.
