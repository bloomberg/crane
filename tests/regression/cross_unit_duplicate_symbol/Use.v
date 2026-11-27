(** A constant defined in one extraction unit and used from another is not
    referenced across the unit boundary: instead of including the library's
    header, the consuming unit re-declares [Lib] and re-emits the body of
    [Lib.len] in its own .cpp.  Linking the two units together then fails with
    a duplicate symbol for [Lib::len]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.NatInt.
From CraneTestsRegression Require Import cross_unit_duplicate_symbol.Lib.

Module Use.
  Definition two : Lib.lst := Lib.Cons 1 (Lib.Cons 2 Lib.Nil).

  Definition answer : nat := Lib.len two.
End Use.

Crane Extraction "cross_unit_duplicate_symbol" Use.
