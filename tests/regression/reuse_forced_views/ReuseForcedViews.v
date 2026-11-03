(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Loops under Crane Reuse that read what they walk through borrowed
    views, and that failed to compile.

    [carry] walks its list with the Perceus reuse cursor, which borrows the
    cell it stands on: a match on a field of that cell -- the tree [u] --
    took it apart destructively, through [v_mut()], which a [const] view
    does not offer.  [combine]'s machine enters a local fixpoint that reads
    the tail [l] of the cell its enclosing turn took apart, kept in the
    frame by reference: the push passing [l] on named the pointer the
    enclosing turn had bound, which the fixpoint's own turn does not
    have. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Module ReuseForcedViews.

Inductive tree : Type :=
| Leaf : tree
| Node : nat -> tree -> tree -> tree.

Definition smash (t u : tree) : tree :=
  match t, u with
  | Node x t1 Leaf, Node y u1 Leaf =>
    if Nat.ltb y x then Node x (Node y u1 t1) Leaf else Node y (Node x t1 u1) Leaf
  | _, _ => Leaf
  end.

Fixpoint carry (q : list tree) (t : tree) : list tree :=
  match q, t with
  | [], Leaf => []
  | [], _ => [t]
  | Leaf :: q', _ => t :: q'
  | u :: q', Leaf => u :: q'
  | u :: q', Node _ _ _ => Leaf :: carry q' (smash t u)
  end.

Fixpoint combine (m : list (nat * nat)) : list (nat * nat) -> list (nat * (option nat * option nat)) :=
  match m with
  | [] => map (fun p => (fst p, (None, Some (snd p))))
  | (k, e) :: l =>
    fix combine_aux (m' : list (nat * nat)) : list (nat * (option nat * option nat)) :=
      match m' with
      | [] => map (fun p => (fst p, (Some (snd p), None))) m
      | (k', e') :: l' =>
        if Nat.ltb k k' then (k, (Some e, None)) :: combine l m'
        else if Nat.eqb k k' then (k, (Some e, Some e')) :: combine l l'
        else (k', (None, Some e')) :: combine_aux l'
      end
  end.

End ReuseForcedViews.

Set Crane Loopify.
Set Crane NonAtomicRc.
Set Crane Reuse.
Crane Extraction "reuse_forced_views" ReuseForcedViews.
