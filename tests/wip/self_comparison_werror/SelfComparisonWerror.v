From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    [Nat.leb n n] (and [Nat.eqb n n], [Nat.ltb n n]) prints [n <= n]; clang's
    -Wtautological-compare rejects that under the test suite's -Werror.  The
    value is right; the generated code does not build with Crane's own flags. *)
Module SelfComparisonWerror.

Definition le_self (n : nat) : bool := Nat.leb n n.
Definition eq_self (n : nat) : bool := Nat.eqb n n.
Definition lt_self (n : nat) : bool := Nat.ltb n n.

End SelfComparisonWerror.

Crane Extraction "self_comparison_werror" SelfComparisonWerror.
