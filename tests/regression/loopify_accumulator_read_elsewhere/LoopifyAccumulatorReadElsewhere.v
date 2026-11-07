From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

(** A tail loop moves a parameter into its own next value only where that
    value reads it for the last time in the turn
    (Ownership_ir.continue_moves). *)
Module LoopifyAccumulatorReadElsewhere.

Inductive tree : Type :=
| leaf : tree
| node : tree -> nat -> tree -> tree.

Fixpoint size (t : tree) : nat :=
  match t with
  | leaf => 0
  | node l _ r => size l + 1 + size r
  end.

Fixpoint keys (t : tree) : nat :=
  match t with
  | leaf => 0
  | node l x r => keys l + x + keys r
  end.

(** Rebuilt around itself in a turn under a match on a nat, which is spelled
    as an [if]: the one read is the turn's last, and is moved. *)
Fixpoint grow (n : nat) (acc : tree) : tree :=
  match n with
  | O => acc
  | S m => grow m (node acc m leaf)
  end.

(** Read twice by its own next value and once more by the count's: no read
    is the turn's last, and none is moved. *)
Fixpoint grow_counted (n : nat) (acc : tree) (count : nat) : nat * tree :=
  match n with
  | O => (count, acc)
  | S m => grow_counted m (node acc m acc) (count + size acc)
  end.

(** Rebuilt around itself in a turn under a match on another parameter,
    whose parts the same next value reads. *)
Fixpoint graft (t : tree) (acc : tree) : tree :=
  match t with
  | leaf => acc
  | node l x r => graft r (node acc x l)
  end.

Definition test_grow_size : nat := size (grow 3 leaf).

Definition test_counted : nat * tree := grow_counted 3 leaf 0.
Definition test_counted_count : nat := fst test_counted.
Definition test_counted_size : nat := size (snd test_counted).

Definition test_graft : tree := graft (node (node leaf 1 leaf) 2 (node leaf 3 leaf)) leaf.
Definition test_graft_size : nat := size test_graft.
Definition test_graft_keys : nat := keys test_graft.

End LoopifyAccumulatorReadElsewhere.

Crane Extraction "loopify_accumulator_read_elsewhere" LoopifyAccumulatorReadElsewhere.
