(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

(** An inner fixpoint, loopified, calling itself and its enclosing fixpoint
    in non-tail positions -- the shape of [FMapAVL.join]'s [join_aux]. *)
Module LoopifyInnerFixSelfCall.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Definition node (l : tree) (x : nat) (r : tree) : tree := Node l x r.

Fixpoint size (t : tree) : nat :=
  match t with Leaf => 0 | Node l _ r => S (size l + size r) end.

Definition add (x : nat) (r : tree) : tree := node Leaf x r.

(** As [FMapAVL.join]: each branch is a function of the remaining
    arguments, and the [Node] branch is the inner fixpoint itself. *)
Fixpoint join (l : tree) : nat -> tree -> tree :=
  match l with
  | Leaf => add
  | Node ll lx lr => fun x =>
    fix join_aux (r : tree) : tree :=
      match r with
      | Leaf => node l x Leaf
      | Node rl rx rr =>
        if Nat.ltb (size rr) lx then node ll lx (join lr x r)
        else if Nat.ltb lx (size rl) then node (join_aux rl) rx rr
        else node l x r
      end
  end.

End LoopifyInnerFixSelfCall.

Set Crane Loopify.
Crane Extraction "loopify_inner_fix_self_call" LoopifyInnerFixSelfCall.
