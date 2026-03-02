(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: canonical structures — instance resolution via unification. *)

From Stdlib Require Import Nat Bool.

Module CanonStruct.

Record EqType := mkEqType {
  carrier : Type;
  eqb : carrier -> carrier -> bool
}.

Canonical nat_eqType := mkEqType nat Nat.eqb.
Canonical bool_eqType := mkEqType bool Bool.eqb.

Definition same {E : EqType} (x y : carrier E) : bool := eqb E x y.

Definition test_nat : bool := same 3 5.
Definition test_bool : bool := same true false.

End CanonStruct.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "canon_struct" CanonStruct.
