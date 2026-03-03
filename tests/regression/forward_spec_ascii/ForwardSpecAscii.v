(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Bug 4: same-module helper forward specs must be emitted before methods use them. *)

From Stdlib Require Import Nat.

Module ForwardSpecAscii.

Inductive node : Type :=
| ANode : nat -> node
| BNode : nat -> node.

Definition helper_nat (n : nat) : nat := S n.

Definition bump_node (x : node) : nat :=
  match x with
  | ANode n => helper_nat n
  | BNode n => helper_nat n
  end.

Definition t : nat := bump_node (ANode 2).

End ForwardSpecAscii.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "forward_spec_ascii" ForwardSpecAscii.
