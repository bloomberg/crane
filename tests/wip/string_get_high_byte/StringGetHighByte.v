(** Found by Ephyra (round 19). [PrimString.get] of a byte at or above 128.

    Rocq's [char63] is an unsigned 63-bit integer below 256, so [get "é" 0]
    (UTF-8 bytes 0xC3 0xA9) is 195 and compares above [get "a" 0] = 97.

    Expected: [first_code = 195] and [high_above_low = true].

    Actual: [first_code = 9223372036854775747] (2^63 - 61) and
    [high_above_low = false]. [char63] is mapped to C++ [char], which is
    signed: the byte reads as -61, sign-extends when it is used as an
    [int63] ([int64_t]), and the 63-bit mask of the int63 operations turns
    it into 2^63 - 61; compared directly it is below 97. Also on main
    (legacy [Mapping.Std]), so not introduced by typed mappings. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Extraction.
From Stdlib Require Import ZArith Uint63.
From Corelib Require Import PrimString.

Module StringGetHighByte.

Definition accented : PrimString.string := "é"%pstring.

Definition first_code : nat := Z.to_nat (Uint63.to_Z (PrimString.get accented 0)).

Definition high_above_low : bool :=
  PrimInt63.ltb (PrimString.get "a"%pstring 0) (PrimString.get accented 0).

End StringGetHighByte.

Crane Extraction "string_get_high_byte" StringGetHighByte.
