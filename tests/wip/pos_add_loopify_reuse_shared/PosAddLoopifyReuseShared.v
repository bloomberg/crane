From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List PArith NArith.
Import ListNotations.
Set Crane Loopify.
Set Crane Reuse.
Set Crane SharedVariant.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Wrong value, no diagnostic.  With Loopify, Reuse and SharedVariant all on
    (any two are fine), Stdlib's [Pos.add 9 19] is [20] in C++ instead of
    [28] (so [N.add 9 19] too, without any N mapping); [Pos.add 1 1],
    [Pos.add 3 1], [Pos.succ 7] are right.  The mutually recursive
    [Pos.add]/[Pos.add_carry] run as explicit-stack frames reusing their
    matched cells in place.  No sanitizer report. *)
Module PosAddLoopifyReuseShared.

Definition a : nat := Pos.to_nat (Pos.add 9 19).
Definition b : nat := N.to_nat (N.add 9%N 19%N).
Definition c : nat := Pos.to_nat (Pos.add 1 1).

End PosAddLoopifyReuseShared.

Crane Extraction "pos_add_loopify_reuse_shared" PosAddLoopifyReuseShared.
