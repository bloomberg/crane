(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** [Set Crane NonAtomicRc] with [Set Crane SharedVariant] and
    [Set Crane Format Style "None"]: [shared_variant.h] is emitted ahead of
    [rc.h] (which clang-format would otherwise sort first) and must include
    [<atomic>] itself for [std::memory_order_acquire]. *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module AtomicInclude.

Inductive tree : Type := Leaf | Node (l r : tree).

Fixpoint size (t : tree) : nat :=
  match t with Leaf => 1 | Node l r => size l + size r end.

Definition sample : nat := size (Node (Node Leaf Leaf) Leaf).

End AtomicInclude.

Set Crane Format Style "None".
Set Crane NonAtomicRc.
Set Crane SharedVariant.
Crane Extraction "atomic_include" AtomicInclude.
