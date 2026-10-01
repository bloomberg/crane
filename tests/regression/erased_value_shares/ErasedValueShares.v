From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** An erased value is shared, not copied.  The payload of a [sigT] over
    [Type] has no C++ type and is erased to [crane::obj]; copying the box
    must copy a handle, not the list it holds, and reading it back from a
    named box must not copy either. *)
Module ErasedValueShares.

  Definition packed : {T : Type & T} := existT (fun T => T) (list nat) (seq 0 1000).

  Definition boxes : list {T : Type & T} := [packed; packed].

End ErasedValueShares.

Crane Extraction "erased_value_shares" ErasedValueShares.
