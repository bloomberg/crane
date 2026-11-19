From Crane Require Extraction.
From Crane Require Import Mapping.ZInt.
From Stdlib Require Import Arith.PeanoNat BinNat BinPos BinInt.

(** [compare] and [eq_dec] on numbers mapped to machine integers become
    native comparisons.  The structural versions count both arguments down
    to zero, so the large values in the test would take hours ([compare])
    or overflow the stack ([eq_dec]). *)

Module NativeNumberCompare.

Definition code (c : comparison) : nat :=
  match c with Lt => 0 | Eq => 1 | Gt => 2 end.

Definition nat_cmp (a b : nat) : nat := code (Nat.compare a b).
Definition nat_cmp' (a b : nat) : nat := code (PeanoNat.Nat.compare a b).
Definition nat_dec (a b : nat) : bool :=
  if PeanoNat.Nat.eq_dec a b then true else false.

Definition n_cmp (a b : N) : nat := code (N.compare a b).
Definition n_dec (a b : N) : bool := if N.eq_dec a b then true else false.

Definition pos_cmp (a b : positive) : nat := code (Pos.compare a b).
Definition pos_dec (a b : positive) : bool :=
  if Pos.eq_dec a b then true else false.

Definition z_cmp (a b : Z) : nat := code (Z.compare a b).
Definition z_dec (a b : Z) : bool := if Z.eq_dec a b then true else false.

(** [compare] passed as a value rather than called. *)
Definition apply_cmp (f : nat -> nat -> comparison) (a b : nat) : nat :=
  code (f a b).
Definition nat_cmp_value (a b : nat) : nat := apply_cmp Nat.compare a b.

End NativeNumberCompare.

Crane Extraction "native_number_compare" NativeNumberCompare.
