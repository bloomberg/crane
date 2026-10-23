(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A tail-recursive local fixpoint inside another one.

    Loopify turned [outer] into a loop and never looked inside the loop it
    made for local fixpoints: [inner] counted down through a lambda calling
    itself, one C++ stack frame per step. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Module LoopifyNestedLocalFix.

Definition count (ns : list nat) : nat :=
  let fix outer (ms : list nat) (acc : nat) : nat :=
    match ms with
    | [] => acc
    | m :: rest =>
      let fix inner (k a : nat) : nat :=
        match k with O => a | S k' => inner k' (S a) end in
      outer rest (inner m acc)
    end in
  outer ns 0.

End LoopifyNestedLocalFix.

Crane Extraction "loopify_nested_local_fix" LoopifyNestedLocalFix.
