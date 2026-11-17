(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a reference from a nested module to an outer definition is
    printed with the shortest path that names it from the outer scope,
    without checking what that path names where it is printed.
    - [Sub.f n := 2 * OuterMemberShadowedByNested.f n] is emitted inside
      [Sub] as [2 * f(n)]: [Sub::f] calling itself.  Clang notices only
      because of [-Winfinite-recursion] under [-Werror].
    - [Sub.k := OuterMemberShadowedByNested.k + 1] is emitted as
      [static inline const uint64_t k = (k + 1);], which initialises [k]
      from itself, silently.
    - A module [Node] next to a constructor [Node]: inside the methodified
      [sum], [Node.bonus] is printed as [Node::bonus], which names the
      constructor's struct [tree::Node]. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module OuterMemberShadowedByNested.

Definition f (n : nat) : nat := n + 1.
Definition k : nat := 10.

Module Sub.
  Definition f (n : nat) : nat := 2 * OuterMemberShadowedByNested.f n.
  Definition k : nat := OuterMemberShadowedByNested.k + 1.
End Sub.

Definition shadowed : nat := Sub.f 3 + Sub.k.

Module Node. Definition bonus : nat := 7. End Node.

Inductive tree := Leaf | Node : tree -> nat -> tree -> tree.

Fixpoint sum (t : tree) : nat :=
  match t with Leaf => Node.bonus | Node l x r => sum l + x + sum r end.

Inductive reader := Reader : (nat -> nat) -> reader.
Definition read_with (t : tree) : reader := Reader (fun x => x + sum t).

Definition with_bonus : nat := sum (Node Leaf 1 Leaf) + match read_with Leaf with Reader g => g 0 end.

End OuterMemberShadowedByNested.

Crane Extraction "outer_member_shadowed_by_nested" OuterMemberShadowedByNested.
