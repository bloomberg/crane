(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A [fold_right] callback of the form [fun f acc => f acc].  It is
    eta-reduced to a one-argument lambda, which no longer satisfies the
    two-argument constraint on the generated [fold_right]. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import NatIntStd.
Require Import List.
Import ListNotations.

Module EtaFoldCallback.
Inductive box := Box : list nat -> box.
Definition grab (b : box) : nat -> nat :=
  match b with Box l => fun k => fold_right Nat.add k l end.
Definition run : nat :=
  let fs := map (fun n => grab (Box [n; n+1])) [1;2;3] in
  fold_right (fun f acc => f acc) 0 fs.
End EtaFoldCallback.

Crane Extraction "eta_fold_callback" EtaFoldCallback.
