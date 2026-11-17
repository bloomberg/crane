(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Numeral converters applied to digit chains.  A signed chain is not read
    as an unsigned one, and a converter returning an [option] is not folded
    into a bare literal of the numeral type. *)

From Stdlib Require Import BinInt.
From Crane Require Import Mapping.Std Mapping.NatIntStd Mapping.ZInt.

Module NumeralConverterKind.

Definition z_minus_one : Z :=
  Z.of_num_int (Number.IntDecimal (Decimal.Neg (Decimal.D1 Decimal.Nil))).

Definition z_minus_ten_hex : Z :=
  Z.of_num_int (Number.IntHexadecimal (Hexadecimal.Neg (Hexadecimal.Da Hexadecimal.Nil))).

Definition z_plus_twelve : Z :=
  Z.of_num_int (Number.IntDecimal (Decimal.Pos (Decimal.D1 (Decimal.D2 Decimal.Nil)))).

Definition z_uint : Z :=
  Z.of_num_uint (Number.UIntDecimal (Decimal.D4 (Decimal.D2 Decimal.Nil))).

Definition nat_big : nat := 10000.

Definition nat_of_pos : option nat :=
  Nat.of_num_int (Number.IntDecimal (Decimal.Pos (Decimal.D7 Decimal.Nil))).

Definition nat_of_neg : option nat :=
  Nat.of_num_int (Number.IntDecimal (Decimal.Neg (Decimal.D7 Decimal.Nil))).

End NumeralConverterKind.

Crane Extraction "numeral_converter_kind" NumeralConverterKind.
