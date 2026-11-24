(** Found by Ephyra round 24 (under [CRANE_LOOPIFY_CENSUS], which turns
    Loopify on everywhere; [Set Crane Loopify] is enough). Under Loopify
    and SharedVariant, a recursion over a list whose [cons] case folds a
    one-element list with a step that matches on the tail [r], starting
    from a [match] on [r] whose [cons] branch is the recursive call [g r].
    The ownership check under [CRANE_CHECK_IR] finds the frame's
    continuation reading a value it already moved.  Without SharedVariant,
    or without Loopify, it extracts.

    Expected: extracts under [CRANE_CHECK_IR]; [size (g [1; 2; 3]) = 1].
    Actual: "Crane IR check (moved value read): in
    LoopifySharedVariantMovedRead.g, k is read after it is moved". *)
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Extraction.
From Stdlib Require Import List.
Import ListNotations.

Set Crane Loopify.
Set Crane SharedVariant.

Module LoopifySharedVariantMovedRead.

Inductive tree : Type := Leaf | Node (l : tree) (v : nat) (r : tree).

Fixpoint g (l : list nat) : tree :=
  match l with
  | [] => Leaf
  | _ :: r =>
    fold_left (fun (acc : tree) (_ : nat) => match r with [] => acc | _ :: _ => acc end)
      [1] (match r with [] => Node Leaf 1 Leaf | _ :: _ => g r end)
  end.

Fixpoint size (t : tree) : nat :=
  match t with Leaf => 0 | Node a _ b => S (size a + size b) end.

Definition result : nat := size (g [1; 2; 3]).

End LoopifySharedVariantMovedRead.

Crane Extraction "loopify_shared_variant_moved_read" LoopifySharedVariantMovedRead.
