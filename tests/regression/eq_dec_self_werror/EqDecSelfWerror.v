(** Found by Ephyra round 28. A variant of [self_comparison_werror]
    (regression: [Nat.eqb n n] and kin): [Nat.eq_dec x x] in an [if], seen
    under [Mapping.NatInt] and [Mapping.NatIntBDE], the operands a
    parameter or a [let]-bound variable.

    Expected: compiles with the suite's flags; [result = 1].

    Fixed: written [x == x] (the sumbool is the C++ bool of which side
    holds), which clang's [-Wtautological-compare] rejects under [-Werror].
    The self-comparison fold knew only boolean comparisons by name; it now
    also folds to [left] any constant whose type decides the equality of
    its last two arguments, [forall .., {x = y} + {_}], applied to one
    value. *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.
From Stdlib Require Import Arith.

Module EqDecSelfWerror.

Definition f (x : nat) : nat := if Nat.eq_dec x x then 1 else 2.
Definition result : nat := f 4.

End EqDecSelfWerror.

Crane Extraction "eq_dec_self_werror" EqDecSelfWerror.
