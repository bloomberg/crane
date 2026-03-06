(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: constructor match with nat fallback default. *)

From Stdlib Require Import Nat.

Module MatchFallbackNat.

Inductive maybe_nat : Type :=
| SomeNat : nat -> maybe_nat
| NoneNat : maybe_nat.

Definition fallback (x : maybe_nat) : nat :=
  match x with
  | SomeNat n => n
  | NoneNat => 0
  end.

Definition t : nat :=
  fallback NoneNat + fallback (SomeNat 7).

End MatchFallbackNat.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "match_fallback_nat" MatchFallbackNat.
