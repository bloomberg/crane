(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A module type whose parameter mentions a type declared in the enclosing
    module.  The concept is emitted before the enclosing namespace, so the
    [requires] clause names an identifier that is not declared yet. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import NatIntStd.

Module ModtypeLocalTypeRef.

Definition key := nat.
Definition entry := (key * nat)%type.

Record point := { px : nat ; py : nat }.

Module Type STORE.
  Parameter lookup : entry -> key -> nat.
End STORE.

Module Type SHIFT.
  Parameter shift : point -> nat -> point.
End SHIFT.

Module S : STORE.
  Definition lookup (e : entry) (k : key) : nat :=
    if Nat.eqb (fst e) k then snd e else 0.
End S.

Module T : SHIFT.
  Definition shift (p : point) (d : nat) : point :=
    {| px := px p + d ; py := py p |}.
End T.

Definition run : nat := S.lookup (1, 42) 1 + px (T.shift {| px := 1 ; py := 2 |} 3).

End ModtypeLocalTypeRef.

Crane Extraction "modtype_local_type_ref" ModtypeLocalTypeRef.run.
