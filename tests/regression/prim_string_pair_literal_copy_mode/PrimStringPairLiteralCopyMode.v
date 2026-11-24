(** Found by Ephyra round 24. A [match] on a pair literal whose first
    component is a primitive string literal, under [Mapping.Std]
    (primitive strings as [std::string]): the match is reduced to binding
    the field, [std::string p = "ab"; return p;], and the copy-mode check
    under [CRANE_CHECK_IR] reported the ownership plan copying [p] where
    its declaration clones it.  The C++ was right.  The generator found it
    also through a [sum] literal ([of_sum]) and a list literal
    ([of_list]).  Fixed: [p]'s Core type is the literal's
    ([Core.Type.String]), which the ownership plan ([Ownership_ir.Region])
    took for bits, while C++ spells it as the primitive-string mapping's
    type, which a copy clones; the plan now reads it as that mapping's
    type, as a parameter of type [PrimString.string] already was.

    Expected: extracts under [CRANE_CHECK_IR]; [len 0 = 2],
    [of_sum 0 = "cd"], [of_list 0 = "f"]. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Corelib Require Import PrimString.
From Stdlib Require Uint63 BinInt.
From Crane Require Import Extraction.
From Stdlib Require Import List.
Import ListNotations.

Module PrimStringPairLiteralCopyMode.

Definition first (n : nat) : PrimString.string :=
  match ("ab"%pstring, n) with (p, _) => p end.

Definition of_sum (n : nat) : PrimString.string :=
  match (@inl PrimString.string nat "cd"%pstring) with inl p => p | inr _ => ""%pstring end.

Definition of_list (n : nat) : PrimString.string :=
  match ["e"%pstring; "f"%pstring] with [] => ""%pstring | [h] => h | _ :: h :: _ => h end.

Definition len (n : nat) : nat := BinInt.Z.to_nat (Uint63.to_Z (PrimString.length (first n))).

End PrimStringPairLiteralCopyMode.

Crane Extraction "prim_string_pair_literal_copy_mode" PrimStringPairLiteralCopyMode.
