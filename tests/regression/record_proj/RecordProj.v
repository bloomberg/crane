(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*
   This test exposes the "TODOrecordProj" fallback strings at:
   - translation.ml:1617
   - translation.ml:1636
   - translation.ml:1653
   - translation.ml:1684

   These occur when record field access doesn't match expected patterns,
   such as when trying to access fields out of bounds or with complex patterns.
*)
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import Lia.
Require Crane.Extraction.

Module RecordProj.

(* A simple record type *)
Record Point := mkPoint {
  x : nat;
  y : nat
}.

(* A record with erased fields (Props) that might cause indexing issues *)
Record ComplexRecord := mkComplex {
  field1 : nat;
  prop_field : field1 > 0; (* This gets erased *)
  field2 : nat;
  another_prop : field2 < 100; (* This gets erased *)
  field3 : nat
}.

(* Try to access fields in unusual ways that might trigger the fallback *)
Definition weird_access (p : Point) : nat :=
  match p with
  | mkPoint a b =>
      (* This might create an unusual pattern that doesn't match
         the expected MLrel i or MLapp (MLrel i, args) patterns *)
      let sum := a + b in
      sum + a
  end.

(* Access complex record with erased fields *)
Definition complex_access (c : ComplexRecord) : nat :=
  match c with
  | mkComplex f1 _ f2 _ f3 => f1 + f2 + f3
  end.

(* Nested match on record - might create unusual patterns *)
Definition nested_record_match (p1 p2 : Point) : nat :=
  match p1 with
  | mkPoint x1 y1 =>
      match p2 with
      | mkPoint x2 y2 => x1 + y1 + x2 + y2
      end
  end.

(* Function that might create MLapp with unusual arguments *)
Definition apply_to_field (f : nat -> nat) (p : Point) : nat :=
  match p with
  | mkPoint a b => f a + f b
  end.

Definition test1 := weird_access (mkPoint 10 20).
(* Provide actual proofs for the prop fields *)
Lemma proof1 : 5 > 0. Proof. lia. Qed.
Lemma proof2 : 10 < 100. Proof. lia. Qed.
Definition test2 := complex_access (mkComplex 5 proof1 10 proof2 15).

End RecordProj.

Crane Extraction "record_proj" RecordProj.
