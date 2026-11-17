(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** A partial application passed as a function ([fold_left (step (cost xs))
    xs 0]) is eta-expanded into a lambda.  Its already-applied arguments
    are evaluated once, where the lambda is made, not at each call. *)
From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

(** Counted by the test: [eta_tick] is in eta_tick.h. *)
Definition tick (n : nat) : nat := n.
Crane Extract Inlined Constant tick => "eta_tick(%a0)" From "eta_tick.h".

Module EtaArg.

Definition cost (xs : list nat) : nat := tick (length xs).

Definition step (k acc x : nat) : nat := acc + x + k.

Definition total (xs : list nat) : nat := fold_left (step (cost xs)) xs 0.

End EtaArg.

Crane Extraction "eta_arg" EtaArg.
