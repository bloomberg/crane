From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.

(** A module whose name is the one Crane picks for a generated type — [Nat] for
    Rocq's [nat], [Bool0] for [bool] — is emitted as a struct nested inside
    that type, giving "member 'ModuleNamedLikeGeneratedType' has the same name
    as its class".  The clash is with a name Crane invented, so no amount of
    care on the Rocq side avoids it. *)

Module Nat.
  Definition k : nat := 1.
End Nat.

Module ModuleNamedLikeGeneratedType.
  Definition run : nat := Nat.k.
End ModuleNamedLikeGeneratedType.

Crane Extraction "module_named_like_generated_type" ModuleNamedLikeGeneratedType.
