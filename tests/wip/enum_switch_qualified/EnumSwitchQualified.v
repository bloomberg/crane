(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Bug 6: enum switch generation must preserve correct module qualification. *)

From Stdlib Require Import Nat.

Module EnumSwitchQualified.

Module Outer.
  Inductive color : Type := Red | Blue.

  Definition flip (c : color) : color :=
    match c with
    | Red => Blue
    | Blue => Red
    end.

  Definition code (c : color) : nat :=
    match c with
    | Red => 1
    | Blue => 2
    end.
End Outer.

Definition t : nat := Outer.code (Outer.flip Outer.Red).

End EnumSwitchQualified.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "enum_switch_qualified" EnumSwitchQualified.