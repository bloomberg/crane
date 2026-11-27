From Stdlib Require Import Arith.PeanoNat List.
Import ListNotations.
From Crane Require Import Mapping.Std Mapping.NatInt.
From Crane Require Extraction.

(** An inner [fix] that calls the outer function.

    [rose_sum] folds over a rose tree's children with a nested [fix sum_list]
    that recurses back into the outer [rose_sum].  The nested fixpoint is
    adopted as a second entry point of [rose_sum]'s frame machine, so both
    recursions push onto one stack and the extracted [rose_sum] has no C++
    self-call. *)

Set Crane Loopify.

Module LoopifyGapNestedFix.

Inductive rose : Type := Rose : nat -> list rose -> rose.

Fixpoint rose_sum (r : rose) : nat :=
  match r with
  | Rose n children =>
    n + (fix sum_list (l : list rose) : nat :=
           match l with
           | [] => 0
           | x :: xs => rose_sum x + sum_list xs
           end) children
  end.

(** A fixed sample tree so the test driver need not build [list rose] in C++.
    Sum of all labels: 1 + 2 + 3 + 4 = 10. *)
Definition sample_tree : rose :=
  Rose 1 [Rose 2 []; Rose 3 [Rose 4 []]].

Definition rose_sum_sample (_ : unit) : nat := rose_sum sample_tree.

End LoopifyGapNestedFix.

Crane Extraction "loopify_gap_nested_fix"
  LoopifyGapNestedFix.rose_sum
  LoopifyGapNestedFix.rose_sum_sample.
