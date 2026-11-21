(** Found by Ephyra (round 19). [Mapping.AsciiChar] imported without
    [Mapping.Std] (so [bool] is not mapped to C++ [bool]).

    Expected: the program compiles and [code_is_66] is [true]: the character
    with bits 0100 0010 is 66.

    Actual: C++ compile error "value of type 'Bool0' is not contextually
    convertible to 'bool'". The mapping's constructor template packs the
    eight fields with [%a0 ? 1 : 0] and its match view produces C++ [bool]s,
    both assuming [bool] is C++ [bool]; unmapped, [bool] is the generated
    enum [Bool0]. Also on main (legacy [AsciiChar]). *)
From Crane Require Import Mapping.AsciiChar.
From Crane Require Extraction.
From Stdlib Require Import Ascii.

Module AsciiCharWithoutBoolMapping.

Definition c : ascii := Ascii false true false false false false true false.

Definition code_is_66 : bool := Nat.eqb (nat_of_ascii c) 66.

End AsciiCharWithoutBoolMapping.

Crane Extraction "ascii_char_without_bool_mapping" AsciiCharWithoutBoolMapping.
