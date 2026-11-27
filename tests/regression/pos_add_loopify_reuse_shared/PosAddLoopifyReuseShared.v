From Crane Require Import Mapping.NatInt.
From Crane Require Extraction.
From Stdlib Require Import List PArith NArith.
Import ListNotations.
Set Crane Loopify.
Set Crane Reuse.
Set Crane SharedVariant.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Was a wrong value, no diagnostic.  With Loopify, Reuse and SharedVariant
    all on (any two were fine), Stdlib's [Pos.add 9 19] was [20] in C++
    instead of [28] (so [N.add 9 19] too, without any N mapping);
    [Pos.add 1 1], [Pos.add 3 1], [Pos.succ 7] were right.  No sanitizer
    report.

    The mutually recursive [Pos.add]/[Pos.add_carry] run as one machine,
    [add_carry] adopted as an entry taking its arguments by value.  Its
    handler matched them through [v_mut()], which copies a shared block, and
    pushed a [_call] of [add] pointing into the copy's fields; the copy died
    with the handler and the pool gave its memory to the next block. *)
Module PosAddLoopifyReuseShared.

Definition a : nat := Pos.to_nat (Pos.add 9 19).
Definition b : nat := N.to_nat (N.add 9%N 19%N).
Definition c : nat := Pos.to_nat (Pos.add 1 1).
Definition d : nat := Pos.to_nat (Pos.add_carry 9 19).
Definition e : nat := Pos.to_nat (Pos.add 255 1).
Definition f : nat := Pos.to_nat (Pos.add 1023 1025).

(** Sums of positives built at run time, so held once, across every carry. *)
Definition pos_add (x y : nat) : nat :=
  Pos.to_nat (Pos.add (Pos.of_succ_nat x) (Pos.of_succ_nat y)).
Definition pos_add_carry (x y : nat) : nat :=
  Pos.to_nat (Pos.add_carry (Pos.of_succ_nat x) (Pos.of_succ_nat y)).
Definition n_add (x y : nat) : nat := N.to_nat (N.add (N.of_nat x) (N.of_nat y)).

End PosAddLoopifyReuseShared.

Crane Extraction "pos_add_loopify_reuse_shared" PosAddLoopifyReuseShared.
