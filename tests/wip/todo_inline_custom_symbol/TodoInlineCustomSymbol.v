(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: direct inlined function symbols should not need spurious eta wrapping. *)

From Stdlib Require Import Nat.

Module TodoInlineCustomSymbol.

Parameter foreign_inc : nat -> nat.

Definition alias : nat -> nat :=
  foreign_inc.

Definition twice (n : nat) : nat :=
  alias (alias n).

Definition test_value : nat :=
  twice 3.

End TodoInlineCustomSymbol.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extract Inlined Constant TodoInlineCustomSymbol.foreign_inc => "inline_inc_impl" From "todo_inline_custom_symbol_support.h".
Crane Extraction "todo_inline_custom_symbol" TodoInlineCustomSymbol.
