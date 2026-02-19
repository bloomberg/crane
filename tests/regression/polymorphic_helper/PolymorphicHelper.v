(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import Lists.List.
Import ListNotations.

Definition foo (n : nat) (b : bool) : nat :=
  let aux {A : Type} (a : A) : nat :=
    List.length (List.repeat a n)
  in aux n + aux b.

Require Crane.Extraction.
Require Crane.Mapping.Std.
Crane Extraction "polymorphic_helper" foo.
