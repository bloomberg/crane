(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Bug 9: header/source signature parity for extracted helper functions. *)

From Stdlib Require Import Nat.

Module SignatureParityFix.

Definition f (seed : nat) : nat :=
  let fix aux (n : nat) : nat :=
      match n with
      | O => seed
      | S n' => aux n'
      end
  in aux (S seed).

Definition t : nat := f 4.

End SignatureParityFix.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "signature_parity_fix" SignatureParityFix.