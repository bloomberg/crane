(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: exercises caller-owned scoped arenas (crane::arena_use_scope) and the
   debug-build fallback-growth warning, on a recursive tree extracted in arena
   mode. *)
From Stdlib Require Import Lists.List.
Import ListNotations.

Module Tree.

Inductive tree (A : Type) : Type :=
| leaf : tree A
| node : tree A -> A -> tree A -> tree A.

Arguments leaf {A}.
Arguments node {A} t1 x t2.

Fixpoint size {A} (t : tree A) : nat :=
  match t with
  | leaf => 1
  | node l _ r => 1 + size l + size r
  end.

End Tree.

Require Crane.Extraction.
(* Scoped-arena redesign: no per-type arena directive. Arena backing comes from
   the caller-owned crane::arena_use_scope installed in arena_scoping.t.cpp. *)
Crane Extraction "arena_scoping" Tree.
