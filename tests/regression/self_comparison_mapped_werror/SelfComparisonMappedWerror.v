From Crane Require Import Mapping.Std Mapping.NatIntStd Mapping.ZInt.
From Crane Require Extraction.
From Stdlib Require Import ZArith PrimInt63.

(** A comparison of one variable with itself under the mappings whose
    guards compare their operands: [Z.geb z z] would print [z >= z] and
    [PrimInt63.eqb i i] [i == i], which -Wtautological-compare rejects
    under -Werror.  Core folds each to its value, as it does [Nat.leb n n]
    (self_comparison_werror). *)
Module SelfComparisonMappedWerror.

Definition z_ge_self (z : Z) : bool := Z.geb z z.
Definition z_gt_self (z : Z) : bool := Z.gtb z z.
Definition i_eq_self (i : int) : bool := PrimInt63.eqb i i.
Definition i_le_self (i : int) : bool := PrimInt63.leb i i.
Definition i_lt_self (i : int) : bool := PrimInt63.ltb i i.

End SelfComparisonMappedWerror.

Crane Extraction "self_comparison_mapped_werror" SelfComparisonMappedWerror.
