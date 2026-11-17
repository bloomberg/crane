(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: [Crane NoLoopify] does not reach a function made a method of
    its inductive.  [size] below becomes [tree::size()] -- read through a
    closure, which is what makes it a method -- and is loopified although
    the command names it: a method's setting is looked up for its
    inductive, never for the function.  The dune rule checks the header for
    the loop. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module NoloopifyMethod.

Inductive tree := Leaf | Node : tree -> tree -> tree.

Fixpoint size (t : tree) : nat :=
  match t with Leaf => 1 | Node l r => size l + size r end.

Inductive reader := Reader : (nat -> nat) -> reader.
Definition read_with (t : tree) : reader := Reader (fun x => x + size t).
Definition read (r : reader) (x : nat) : nat := match r with Reader f => f x end.

Definition result : nat := read (read_with (Node (Node Leaf Leaf) Leaf)) 0.

End NoloopifyMethod.

Crane NoLoopify NoloopifyMethod.size.
Crane Extraction "noloopify_method" NoloopifyMethod.
