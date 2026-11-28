(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A polymorphic definition that only throws and takes no value
    arguments.  It is emitted as a zero-parameter function template, so a
    use must call it: [out_of_fuel<uint64_t>()].  It printed the template
    without the call, [return out_of_fuel<uint64_t>;], which does not
    compile. *)

From Stdlib Require Import PeanoNat.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatInt.
From Corelib Require Import PrimString.
From Crane Require Import Mapping.Std Monads.ITree Monads.Error.
From ITree Require Import Events.Exception.

Module PolyThrowingCall.

Open Scope itree_scope.
Open Scope pstring_scope.

Notation E := (exceptE Err).

Definition out_of_fuel {A} : itree E A := failwith "out of fuel".

Fixpoint count (fuel n : nat) : itree E nat :=
  match fuel with
  | O => out_of_fuel
  | S f => if Nat.eqb n 0 then Ret 0 else ITree.bind (count f (n - 1)) (fun r => Ret (S r))
  end.

Definition flag (fuel : nat) : itree E bool :=
  match fuel with
  | O => out_of_fuel
  | S _ => Ret true
  end.

Definition ok := count 10 3.
Definition flag_ok := flag 1.

End PolyThrowingCall.

Crane Extraction "poly_throwing_call" PolyThrowingCall.
