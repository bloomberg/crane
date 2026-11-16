(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*
   This test tries to trigger the TODOrecordProj fallback by creating
   records with many erased fields that could cause indexing mismatches
   between ids and non_erased_fields.
*)
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import Lia.
Require Crane.Extraction.

Module ErasedRecord.

(* Record with alternating real and erased fields *)
Record ManyProps := mkManyProps {
  field0 : nat;
  prop0 : field0 > 0;
  field1 : nat;
  prop1 : field1 > 0;
  field2 : nat;
  prop2 : field2 > 0;
  field3 : nat;
  prop3 : field3 > 0;
  field4 : nat;
  prop4 : field4 > 0
}.

(* Complex pattern matching on this record *)
Definition complex_match (r : ManyProps) : nat :=
  match r with
  | mkManyProps f0 _ f1 _ f2 _ f3 _ f4 _ =>
      (* Use all fields in a complex way *)
      f0 + f1 + f2 + f3 + f4
  end.

(* Try to create unusual patterns in the match body *)
Definition unusual_body (r : ManyProps) : nat :=
  match r with
  | mkManyProps f0 _ f1 _ f2 _ f3 _ f4 _ =>
      (* Nested match on the same type *)
      match mkManyProps f0 (ltac:(lia)) f1 (ltac:(lia)) f2 (ltac:(lia)) f3 (ltac:(lia)) f4 (ltac:(lia)) with
      | mkManyProps a _ b _ c _ d _ e _ => a + b + c + d + e
      end
  end.

(* Record with mostly Props *)
Record MostlyProps := mkMostlyProps {
  real1 : nat;
  p1 : real1 > 0;
  p2 : real1 < 100;
  p3 : real1 <> 0;
  real2 : nat;
  p4 : real2 > 0;
  p5 : real2 < 100;
  p6 : real2 <> 0;
  real3 : nat;
  p7 : real3 > 0;
  p8 : real3 < 100;
  p9 : real3 <> 0
}.

Definition access_mostly_props (r : MostlyProps) : nat :=
  match r with
  | mkMostlyProps r1 _ _ _ r2 _ _ _ r3 _ _ _ => r1 + r2 + r3
  end.

Definition test1 := complex_match (mkManyProps 1 (ltac:(lia)) 2 (ltac:(lia)) 3 (ltac:(lia)) 4 (ltac:(lia)) 5 (ltac:(lia))).
Definition test2 := unusual_body (mkManyProps 1 (ltac:(lia)) 2 (ltac:(lia)) 3 (ltac:(lia)) 4 (ltac:(lia)) 5 (ltac:(lia))).
Definition test3 := access_mostly_props (mkMostlyProps 5 (ltac:(lia)) (ltac:(lia)) (ltac:(lia)) 10 (ltac:(lia)) (ltac:(lia)) (ltac:(lia)) 15 (ltac:(lia)) (ltac:(lia)) (ltac:(lia))).

End ErasedRecord.

Crane Extraction "erased_record" ErasedRecord.
