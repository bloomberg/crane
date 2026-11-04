(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A value assigned a part of itself, under Crane NonAtomicRc.

    [l = *tail], where [tail] is a field of [l], is ordinary C++ for a value
    type, and std::shared_ptr makes it work: its assignment takes the new
    pointer before it releases the old one.  crane::rc released first, which
    freed the cell holding the very pointer it was about to copy, so the list
    lost its tail.  The pool crane::rc allocates from keeps the freed memory
    mapped, so AddressSanitizer saw nothing; the null pointer read back did. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module FastVariantAssignFromOwnChild.

Inductive chain : Type :=
| Last : nat -> chain
| Link : nat -> chain -> chain.

Fixpoint total (c : chain) : nat :=
  match c with
  | Last n => n
  | Link n rest => n + total rest
  end.

End FastVariantAssignFromOwnChild.

Set Crane NonAtomicRc.
Set Crane FastVariant.
Crane Extraction "fast_variant_assign_from_own_child" FastVariantAssignFromOwnChild.
