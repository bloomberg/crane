From Crane Require Import Mapping.Std.
From Stdlib Require Import Arith PeanoNat.

Inductive raw_id : Set := | Name : nat -> raw_id | Anon : nat -> raw_id.

Definition raw_id_dec : forall x y : raw_id, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.
