From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    [Nat.pred (Nat.max a b)] lowers to [auto &&_once1 = std::max(x, y);]:
    [std::max] returns a reference to one of its temporaries, which dies at
    the end of the full-expression, so the reads of [_once1] are use after
    free (clang's -Wdangling rejects it under -Werror). *)
Module MaxResultDanglingRef.

Definition f (a b : nat) : nat := Nat.pred (Nat.max (a + 1) (b + 2)).

End MaxResultDanglingRef.

Crane Extraction "max_result_dangling_ref" MaxResultDanglingRef.
