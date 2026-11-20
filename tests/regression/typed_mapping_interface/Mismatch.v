(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Compiled interfaces, the refusals: a unit that includes the header of
    [typed_mapping_interface_lib] but resolves [Meter] differently from
    the [Narrow] mapping that header was written against is refused before
    anything is written -- first with no mapping of [Meter] imported, then
    with [Wide]. *)

From Crane Require Import Extraction Mapping.NatIntStd.
From CraneTestsRegression Require Import typed_mapping_interface.Lib.

Module Unmapped.
  Definition quad (m : Meter) : Meter := Lib.double (Lib.double m).
End Unmapped.

Fail Crane Extraction "typed_mapping_interface_unmapped" Unmapped.

Import Wide.

Module Widened.
  Definition quad (m : Meter) : Meter := Lib.double (Lib.double m).
End Widened.

Fail Crane Extraction "typed_mapping_interface_widened" Widened.
