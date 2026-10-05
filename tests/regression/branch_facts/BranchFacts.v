(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

(** Guards a declared operation's mapping keeps, dropped where the
    enclosing branch, or a nonzero divisor, rules their case out -- and kept
    where it does not. *)
Module BranchFacts.

(** Unguarded in both branches: each knows which operand is larger. *)
Definition abs_diff (a b : nat) : nat :=
  if Nat.leb b a then a - b else b - a.

(** Unguarded: [n] is not zero in the [else] branch. *)
Definition pred_or_zero (n : nat) : nat :=
  if Nat.eqb n 0 then 0 else n - 1.

(** Guarded still: the branch knows [a <= b], the wrong way round. *)
Definition wrong_way (a b : nat) : nat :=
  if Nat.leb a b then a - b else 0.

(** Unguarded: the divisor is a nonzero numeral. *)
Definition half (n : nat) : nat := Nat.div n 2.
Definition parity (n : nat) : nat := Nat.modulo n 2.

(** Guarded still: the divisor may be zero. *)
Definition ratio (a b : nat) : nat := Nat.div a b.
Definition rem (a b : nat) : nat := Nat.modulo a b.

(** A match on [bool] returning its own truth value. *)
Definition is_small (n : nat) : bool := if Nat.ltb n 10 then true else false.

End BranchFacts.

Crane Extraction "branch_facts" BranchFacts.
