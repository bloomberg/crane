From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Two branches each build a pair holding a lambda: [std::make_pair(0, [](uint64_t x) {...})]
    deduces a distinct closure type per branch, so the conditional's operands
    (or a lambda's two returns) have incompatible types. *)
Module BranchPairsOfLambdas.

Definition f (b : bool) : nat :=
  fst (if b then (0, fun x : nat => x) else (1, fun x : nat => x + 1)).

End BranchPairsOfLambdas.

Crane Extraction "branch_pairs_of_lambdas" BranchPairsOfLambdas.
