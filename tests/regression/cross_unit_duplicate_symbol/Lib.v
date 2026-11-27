(** The library half of a two-unit extraction: [Lib] is extracted on its own
    into [cross_unit_duplicate_symbol_lib.{h,cpp}]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.NatInt.

Module Lib.
  Inductive lst : Set := Nil | Cons : nat -> lst -> lst.

  Fixpoint len (l : lst) : nat :=
    match l with Nil => 0 | Cons _ r => S (len r) end.
End Lib.

Crane Extraction "cross_unit_duplicate_symbol_lib" Lib.
