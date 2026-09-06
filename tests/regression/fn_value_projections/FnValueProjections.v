(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A polymorphic constant used as a function value rather than applied:
    [map (@id nat) l].  The call spells a template instantiation, while the
    definition was emitted with an erased signature over [std::any]. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import NatIntStd.
Require Import List.
Import ListNotations.

Module FnValueProjections.
Record point := { px : nat ; py : nat }.
Definition xs (l : list point) : list nat := map px l.
Definition firsts (l : list (nat * nat)) : list nat := map fst l.
Definition somes (l : list nat) : list (option nat) := map (@Some nat) l.
Definition ids (l : list nat) : list nat := map (@id nat) l.
Definition run : nat :=
  fold_right Nat.add 0 (xs [ {| px := 1 ; py := 2 |} ])
  + fold_right Nat.add 0 (firsts [(3,4)])
  + length (somes [1;2]) + fold_right Nat.add 0 (ids [5]).
End FnValueProjections.

Crane Extraction "fn_value_projections" FnValueProjections.run.
