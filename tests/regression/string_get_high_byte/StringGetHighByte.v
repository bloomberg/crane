(** Found by Ephyra (round 19). [PrimString.get] of a byte at or above 128.

    Rocq's [char63] is an unsigned 63-bit integer below 256, so [get "é" 0]
    (UTF-8 bytes 0xC3 0xA9) is 195 and compares above [get "a" 0] = 97.

    Expected: [first_code = 195], [high_above_low = true], and
    [wide_code = 295].

    Fixed: [first_code] was 9223372036854775747 (2^63 - 61) and
    [high_above_low] false.  [char63] was mapped to C++ [char], which is
    signed: the byte read as -61 and sign-extended when used as an [int63].
    [char63] is [int] by definition, so it is now mapped to [int64_t], and
    [get] reads the byte unsigned.  Also on main (legacy [Mapping.Std]). *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Extraction.
From Stdlib Require Import ZArith Uint63.
From Corelib Require Import PrimString.

Module StringGetHighByte.

Definition accented : PrimString.string := "é"%pstring.

Definition first_code : nat := Z.to_nat (Uint63.to_Z (PrimString.get accented 0)).

Definition high_above_low : bool :=
  PrimInt63.ltb (PrimString.get "a"%pstring 0) (PrimString.get accented 0).

(** A [char63] is any [int]: one above 255 keeps its value. *)
Definition wide : char63 := PrimInt63.add (PrimString.get accented 0) 100.

Definition wide_code : nat := Z.to_nat (Uint63.to_Z wide).

End StringGetHighByte.

Crane Extraction "string_get_high_byte" StringGetHighByte.
