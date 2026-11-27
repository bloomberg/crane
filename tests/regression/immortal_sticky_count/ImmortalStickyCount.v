(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Set Crane NonAtomicRc] with [Set Crane SingleThreaded]: an immortal
    block's count is sticky rather than tested -- it starts at half the
    range, and copies and drops update it like any other count without ever
    bringing it to zero.  A global's blocks survive any number of copies and
    drops; a value built at run time is counted and freed as before. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.NatInt.

Module ImmortalStickyCount.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint full (d : nat) : tree :=
  match d with O => Leaf | S k => Node (full k) d (full k) end.

Fixpoint size (t : tree) : nat :=
  match t with Leaf => 0 | Node l _ r => S (size l + size r) end.

Definition table : tree := full 4.

(** Built at run time: counted. *)
Definition fresh (d : nat) : tree := full d.

(** [n] uses of the global, each a copy. *)
Fixpoint sizes (n : nat) (acc : nat) : nat :=
  match n with O => acc | S k => sizes k (acc + size table) end.

End ImmortalStickyCount.

Set Crane SharedVariant.
Set Crane NonAtomicRc.
Set Crane SingleThreaded.
Crane Extraction "immortal_sticky_count" ImmortalStickyCount.
