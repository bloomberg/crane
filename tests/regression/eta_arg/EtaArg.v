(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** A partial application passed as a function ([fold_left (step (cost xs))
    xs 0]) is eta-expanded into a lambda.  Its already-applied arguments
    are evaluated once, where the lambda is made, not at each call. *)
From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatInt.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

(** Counted by the test: [eta_tick] is in eta_tick.h. *)
Definition tick (n : nat) : nat := n.
#[global] Instance tick_mapping : OperationMapping (Ref (@tick)) :=
  pure_cpp ["eta_tick.h"] ["n"]
    (Structured (Call "eta_tick" [] [Arg "n"])).

Module EtaArg.

Definition cost (xs : list nat) : nat := tick (length xs).

Definition step (k acc x : nat) : nat := acc + x + k.

Definition total (xs : list nat) : nat := fold_left (step (cost xs)) xs 0.

End EtaArg.

Crane Extraction "eta_arg" EtaArg.
