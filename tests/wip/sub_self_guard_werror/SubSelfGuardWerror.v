From Crane Require Import Mapping.NatIntStd Mapping.NInt.
From Crane Require Extraction.
From Stdlib Require Import List NArith.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Subtraction of a variable from itself: the mapping guard compares the
    variable with itself ([a >= a ? a - a : 0u] for [N.sub a a], [(a - a) > a]
    for [nat]), which -Wtautological-compare rejects under -Werror (the
    comparison forms in self_comparison_werror are fixed).  Values are right. *)
Module SubSelfGuardWerror.

Definition f (a : N) : N := N.sub a a.
Definition g (a : nat) : nat := a - a.

End SubSelfGuardWerror.

Crane Extraction "sub_self_guard_werror" SubSelfGuardWerror.
