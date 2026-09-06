(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A [sigT] whose payload pairs a witness with a function over that same
    witness.  The payload type erases to [std::any], so the pair components
    and the function must agree on the boxed representation; they do not, and
    the extracted code fails to recover the function from the box. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import List.
Import ListNotations.

Module SigtHeteroPayload.
Definition item := @sigT Type (fun T : Type => (T * (T -> nat))%type).
Definition mk (T : Type) (v : T) (f : T -> nat) : item := @existT Type _ T (v, f).
Definition items : list item :=
  [ mk nat 5 (fun n => n) ; mk bool true (fun b => if b then 1 else 0) ].
Definition run : nat :=
  fold_right (fun i acc => match i with existT _ _ (v, f) => f v + acc end) 0 items.
End SigtHeteroPayload.

Crane Extraction "sigt_hetero_payload" SigtHeteroPayload.run.
