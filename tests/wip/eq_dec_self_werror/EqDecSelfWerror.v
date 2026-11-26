(** Found by Ephyra round 28. [Nat.eq_dec x x] in an [if] is written
    [x == x] (the sumbool is the C++ bool of which side holds), and the test
    suite's [-Werror] rejects the self-comparison. [Nat.eqb x x] in the same
    place is folded to [true] and compiles (the fix of round 3's
    [sub_self_guard_werror] family); the sumbool decision is not folded.
    Variant of [self_comparison_werror] (regression: [Nat.eqb n n] and kin). Seen
    under [Mapping.NatIntStd] and [Mapping.NatIntBDE], the operands a
    parameter or a [let]-bound variable. Expected: compiles, [result = 1].
    Actual: "self-comparison always evaluates to true
    [-Werror,-Wtautological-compare]". *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import Arith.

Module EqDecSelfWerror.

Definition f (x : nat) : nat := if Nat.eq_dec x x then 1 else 2.
Definition result : nat := f 4.

End EqDecSelfWerror.

Crane Extraction "eq_dec_self_werror" EqDecSelfWerror.
