(** Found by Ephyra round 24 (under [CRANE_LOOPIFY_CENSUS], which turns
    Loopify on everywhere; [Set Crane Loopify] is enough). Under Loopify, a
    tree recursion [g t s] that passes the string parameter [s] on in its
    [Node] case, and in its [Leaf] case re-matches [t]: the inner [Leaf]
    branch reads [s] inside a [fold_left] step, the dead inner [Node]
    branch passes [inr s] to a local fixpoint.  The ownership check under
    [CRANE_CHECK_IR] finds [s] read after it is moved.  Without Loopify it
    extracts; with the step returning its accumulator instead of [s] it
    still fails.  Not the shape of [loopify_shared_variant_moved_read]
    (filed in the same round), which needs SharedVariant.

    Expected: extracts under [CRANE_CHECK_IR]; [result = 0] ([g] of a leaf
    is [inr ""]).
    Actual: "Crane IR check (moved value read): in
    LoopifyParamMovedRead.g, s is read after it is moved". *)
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Extraction.
From Stdlib Require Import List String.
Import ListNotations.

Set Crane Loopify.

Module LoopifyParamMovedRead.

Inductive tree : Type := Leaf | Node (l : tree) (v : nat) (r : tree).

Fixpoint g (t : tree) (s : string) : sum (list nat) string :=
  match t with
  | Leaf =>
    match t with
    | Leaf => inr (fold_left (fun (_ : string) (_ : bool) => s) [] ""%string)
    | Node _ _ _ =>
      let fix go (l : list nat) (acc : sum (list nat) string) {struct l} : sum (list nat) string :=
        match l with [] => inr ""%string | _ :: _ => acc end
      in go [] (inr s)
    end
  | Node _ _ r => g r s
  end.

Definition result : nat :=
  match g (Node Leaf 1 Leaf) "ab"%string with inl _ => 7 | inr x => String.length x end.

End LoopifyParamMovedRead.

Crane Extraction "loopify_param_moved_read" LoopifyParamMovedRead.
