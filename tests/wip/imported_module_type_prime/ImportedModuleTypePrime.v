(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import Orders Arith Lia.
From Crane Require Import Mapping.NatIntStd Mapping.Std.

(** A module type declared in another library is re-emitted as a concept, but
    its name is copied verbatim instead of being sanitised, so the apostrophe in
    [TotalLeBool'] reaches the C++ output.  The reference in the functor's
    template head is sanitised, to [TotalLeBool_], so the two never agree. *)

Module ImportedModuleTypePrime.

  Module F (X : Orders.TotalLeBool').
    Definition pick (a b : X.t) : X.t := if X.leb a b then a else b.
  End F.

  Module NatOrd <: Orders.TotalLeBool'.
    Definition t := nat.
    Definition leb := Nat.leb.
    Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
    Proof.
      intros. unfold leb. destruct (Nat.leb_spec a1 a2); auto.
      right. apply Nat.leb_le. lia.
    Qed.
  End NatOrd.

  Module FN := F NatOrd.

  Definition test : nat := FN.pick 3 1.

End ImportedModuleTypePrime.

Crane Extraction "imported_module_type_prime" ImportedModuleTypePrime.
