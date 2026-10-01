From Crane Require Import Mapping.Std.
From Stdlib Require Import Arith PeanoNat.

Inductive zed : Set := | Zp : nat -> zed | Zn : nat -> zed.

Definition raw_cmp (x y : zed) : comparison :=
  match x, y with
  | Zp a, Zp b => Nat.compare a b
  | Zn a, Zn b => Nat.compare b a
  | Zp _, Zn _ => Gt
  | Zn _, Zp _ => Lt
  end.
