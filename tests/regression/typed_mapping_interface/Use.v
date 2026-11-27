(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Compiled interfaces, the consumer: [Use] includes the header of
    [typed_mapping_interface_lib], written against [Narrow], and resolves
    [Meter] with [Narrow] too, so it is accepted. *)

From Crane Require Import Extraction Mapping.NatInt.
From CraneTestsRegression Require Import typed_mapping_interface.Lib.
Import Narrow.

Module Use.
  Definition quad (m : Meter) : Meter := Lib.double (Lib.double m).
  Definition answer : nat := Lib.value (quad (meter 3)).
End Use.

Crane Extraction "typed_mapping_interface" Use.
