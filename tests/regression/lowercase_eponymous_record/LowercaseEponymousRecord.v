(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Regression test: eponymous records with lowercase module names generate
    inconsistent C++ naming. The struct definition uses the original casing
    (e.g. [state]) but type references use [String.capitalize_ascii]
    (e.g. [State]), causing compilation failures. *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module LowercaseEponymousRecord.

(* Lowercase module with eponymous record — triggers the naming bug *)
Module state.
  Record state :=
    { x : nat
    ; y : nat
    }.

  Definition set_x (n : nat) (s : state) : state :=
    {| x := n ; y := y s |}.
End state.
Export state.

Definition example := state.set_x 42 {| x := 0; y := 0 |}.

End LowercaseEponymousRecord.

Crane Extraction "lowercase_eponymous_record" LowercaseEponymousRecord.
