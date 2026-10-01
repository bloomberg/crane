From Crane Require Import Mapping.Std.
From Stdlib Require Import Arith PeanoNat.
From CraneTestsRegression Require Import modtype_alias_emitted_before_original.Orig.
From CraneTestsRegression Require Import modtype_alias_emitted_before_original.Alias.

(** The alias has to be reached, not merely declared: a declaration nothing
    names is never emitted, and the test would pass vacuously. *)

Module Make (X : Dec).
  Definition same (a b : X.t) : bool := if X.eq_dec a b then true else false.
End Make.

Module NatDec <: Dec.
  Definition t : Set := nat.
  Definition eq_dec : forall x y : t, {x = y} + {x <> y} := Nat.eq_dec.
End NatDec.

Module MN := Make NatDec.
