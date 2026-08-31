(** [Decimal.uint] is emitted as [struct Uint {};] -- an inductive with all of
    its constructors dropped -- and every use of it then fails:

    {v
      struct Uint {};
      unknown type name 'Uint'
      no viable conversion from 'std::string' to 'String'
    v} *)

Require Crane.Extraction.
Require Import String DecimalString Decimal.

Module EmptyInductiveDecimalUint.

Definition s (n : nat) : string := NilZero.string_of_uint (Nat.to_uint n).

Definition test : nat := String.length (s 42).

End EmptyInductiveDecimalUint.

Crane Extraction "empty_inductive_decimal_uint" EmptyInductiveDecimalUint.
