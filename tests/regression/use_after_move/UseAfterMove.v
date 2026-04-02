(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Regression test for use-after-move bugs in constructor arguments

    Demonstrates the bug where Crane could generate:
      Ctor{std::move(x), std::move(x)->field}

    After std::move(x), the pointer is null, so ->field causes segfault.
*)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module UseAfterMove.

Record State : Type := mkState {
  value : nat;
  data : nat;
  flag : nat
}.

(* Pattern 1: Record with multiple field projections *)
Definition pattern1 (s : State) : State * nat :=
  (s, value s).

(* Pattern 2: Record with two projections *)
Definition pattern2 (s : State) : State * nat * nat :=
  (s, value s, data s).

(* Pattern 3: Nested pair with projections *)
Definition pattern3 (s : State) : (State * nat) * nat :=
  ((s, value s), data s).

(* Pattern 4: Let-bound value used multiple times *)
Definition pattern4 (s1 : State) : State * nat :=
  let s2 := s1 in
  (s2, value s2).

(* Pattern 5: Chain of lets with projections *)
Definition pattern5 (s1 : State) : State * nat :=
  let s2 := s1 in
  let s3 := s2 in
  (s3, value s3).

(* Pattern 6: If-then-else with projections in both branches *)
Definition pattern6 (s : State) : State * nat :=
  if Nat.eqb (flag s) 0 then
    (s, value s)
  else
    (s, data s).

(* Pattern 7: Inline projections in nested tuple *)
Definition pattern7 (s : State) : ((State * nat) * nat) * nat :=
  (((s, value s), data s), flag s).

End UseAfterMove.

Crane Extraction "use_after_move" UseAfterMove.
