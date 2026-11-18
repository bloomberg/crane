From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List Bool ZArith NArith.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    [Nat.leb n n] (and [Nat.eqb n n], [Nat.ltb n n]) prints [n <= n]; clang's
    -Wtautological-compare rejects that under the test suite's -Werror.  The
    value is right; the generated code does not build with Crane's own flags.

    Fixed in Core: [simpl] folds a pure comparison of one variable with
    itself to its value (Nat, N, Pos, Z [leb]/[eqb]/[ltb], [Bool.eqb]). *)
Module SelfComparisonWerror.

Definition le_self (n : nat) : bool := Nat.leb n n.
Definition eq_self (n : nat) : bool := Nat.eqb n n.
Definition lt_self (n : nat) : bool := Nat.ltb n n.

Definition bool_eq_self (b : bool) : bool := Bool.eqb b b.
Definition z_le_self (z : Z) : bool := Z.leb z z.
Definition z_eq_self (z : Z) : bool := Z.eqb z z.
Definition z_lt_self (z : Z) : bool := Z.ltb z z.
Definition n_le_self (x : N) : bool := N.leb x x.
Definition n_eq_self (x : N) : bool := N.eqb x x.
Definition n_lt_self (x : N) : bool := N.ltb x x.
Definition pos_le_self (x : positive) : bool := Pos.leb x x.
Definition pos_eq_self (x : positive) : bool := Pos.eqb x x.
Definition pos_lt_self (x : positive) : bool := Pos.ltb x x.

End SelfComparisonWerror.

Crane Extraction "self_comparison_werror" SelfComparisonWerror.
