From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From ITree Require Import ITree.

(** A coinductive value is one heap node, shared by every copy.  An
    [ITree.iter] loop suspends every step as a thunk that delegates to the
    next step's tree; forcing follows those delegations without copying
    trees, and retargets them, so walking the loop is linear in its length.
    The t.cpp walks 300000 steps, keeps the first node alive while it
    does so the whole forced chain is in memory at once, and then drops it:
    releasing the chain must not recurse once per step. *)
Module CoinductiveNodeSharing.

  Variant voidE : Type -> Type := .

  Definition count_to (k : nat) : itree voidE nat :=
    ITree.iter (fun i => if Nat.leb k i then Ret (inr i) else Ret (inl (S i))) 0.

End CoinductiveNodeSharing.

Crane Extraction "coinductive_node_sharing" CoinductiveNodeSharing.
