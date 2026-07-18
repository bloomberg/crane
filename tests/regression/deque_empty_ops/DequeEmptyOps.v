(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Regression for the DequeList [map]/[flat_map]/[concat] mappings: their
   result element type is inferred from the deque's [value_type], never from
   [%aN.front()], so the operations are total on the empty deque (calling
   [front()] on an empty deque would be undefined behaviour). Each operation is
   wrapped in a function so it is exercised at runtime on both empty and
   non-empty inputs supplied by the test driver (CWE-476 / CWE-125). *)
From Crane Require Import Mapping.NatIntStd Mapping.DequeList.
From Stdlib Require Import Nat List.
Import ListNotations.
Require Crane.Extraction.

Module DequeEmptyOps.

Definition double (n : nat) : nat := n * 2.
Definition dup (n : nat) : list nat := [n; n].

Definition run_map (l : list nat) : list nat := List.map double l.
Definition run_flatmap (l : list nat) : list nat := List.flat_map dup l.
Definition run_concat (l : list (list nat)) : list nat := List.concat l.

End DequeEmptyOps.

Crane Extraction "deque_empty_ops" DequeEmptyOps.
