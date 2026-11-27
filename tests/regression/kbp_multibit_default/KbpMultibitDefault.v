(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: KBP maps multi-bit accumulator values to 15. *)

From Stdlib Require Import Nat Bool.

Module KbpMultibitDefault.

Record state : Type := mkState {
  acc : nat
}.

Definition execute_kbp (s : state) : state :=
  let result :=
    match acc s with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 4 => 3
    | 8 => 4
    | _ => 15
    end in
  mkState result.

Definition sample : state := mkState 3.
Definition t : bool := Nat.eqb (acc (execute_kbp sample)) 15.

End KbpMultibitDefault.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.
Crane Extraction "kbp_multibit_default" KbpMultibitDefault.
