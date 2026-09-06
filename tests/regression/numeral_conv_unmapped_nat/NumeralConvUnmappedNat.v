From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.ZInt.
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

(** [ZInt] maps [Z] to [int64_t] but leaves [nat] as the extracted unary
    inductive, so [Z.of_nat 2] becomes [static_cast<int64_t>(Nat::s(Nat::s(
    Nat::o())))] -- a cast from a struct with no conversion operator.  The
    converter is folded to a cast without checking that its argument was folded
    to a literal too. *)

Module NumeralConvUnmappedNat.

  Definition xs : list Z := [(-5); 3; 0; 7].

  Definition run : Z := List.fold_left Z.add xs 0 + Z.abs (-9) + Z.of_nat 2.

End NumeralConvUnmappedNat.

Crane Extraction "numeral_conv_unmapped_nat" NumeralConvUnmappedNat.
