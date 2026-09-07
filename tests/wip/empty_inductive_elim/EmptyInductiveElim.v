(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.

(** Eliminating an inductive with no constructors is unreachable, and Crane
    emits [[]() { throw std::logic_error("absurd case"); }()] for it.  That
    lambda's deduced return type is [void], so it cannot initialise the value
    the elimination is supposed to produce. *)

Module EmptyInductiveElim.

  Inductive void := .

  Definition absurd (v : void) : nat := match v with end.

  Definition g (o : option void) : nat :=
    match o with Some v => absurd v | None => 0 end.

  Definition test : nat := g None.

End EmptyInductiveElim.

Crane Extraction "empty_inductive_elim" EmptyInductiveElim.
