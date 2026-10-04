From Crane Require Import Mapping.Std.
From Crane Require Extraction.
From CraneTestsRegression Require Import sep_ext_promoted_alias_import.ProvDef sep_ext_promoted_alias_import.ParamsDef.

Section S.
  Context {Pa : Params}.
  Inductive mbit := Bit_ptr (p : ptr) | Bit_byte (n : nat).
  Definition show (m : mbit) : nat :=
    match m with Bit_ptr _ => 0 | Bit_byte n => n end.
End S.

Crane Separate Extraction show.
