(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: [PrimArray.make] with a length above [PrimArray.max_length]
    aborts the program.  Rocq's [make] clamps the length to [max_length]
    (4194303), so [length (make n x)] is total; the [persistent_array(len,
    def)] constructor allocates [len] elements as given, and the vector
    throws [std::length_error] (or [std::bad_alloc] for a smaller oversized
    length), which terminates the program. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
From Corelib Require Import PrimInt63 PrimArray.
From Crane Require Import Mapping.Std.

Module PersistentArrayMakeUnclamped.

Definition huge : array nat := PrimArray.make 9223372036854775807%uint63 0.

Definition len : int := PrimArray.length huge.

End PersistentArrayMakeUnclamped.

Crane Extraction "persistent_array_make_unclamped" PersistentArrayMakeUnclamped.
