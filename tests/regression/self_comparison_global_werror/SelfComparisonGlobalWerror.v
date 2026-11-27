(** Found by Ephyra (round 21). A variant left by the fixes of
    [self_comparison_werror] (rounds 1 and 2): a self-comparison whose
    operand is a top-level constant, [N.eqb f1 f1] and [Nat.leb k k].

    Expected: compiles with the suite's flags; [result = 2].

    Fixed: printed as [f1 == f1] and [k <= k], which clang's
    [-Wtautological-compare] rejects under [-Werror] ("self-comparison
    always evaluates to true").  The self-comparison fold recognised only
    one variable or one projection of it; it now folds any two identical
    pure operands: variables, globals no mapping spells, literals, and
    constructors and calls over them. *)
From Crane Require Import Mapping.NatInt Mapping.ZInt Mapping.NInt.
From Crane Require Extraction.
From Stdlib Require Import List NArith.
Import ListNotations.
Module SelfComparisonGlobalWerror.
Definition f1 : N := 0%N.
Definition k : nat := 3.
Definition result : nat :=
  List.length (filter (fun b => b) [N.eqb f1 f1; Nat.leb k k]).
End SelfComparisonGlobalWerror.
Crane Extraction "self_comparison_global_werror" SelfComparisonGlobalWerror.
