(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*
   ULTRA-EXTREME attempt: Use UNSOUND axioms to create inconsistencies
   that might expose edge cases in extraction.

   WARNING: This uses axioms that make Coq inconsistent!
   This is ONLY for testing extraction edge cases.
*)
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module UnsoundAxioms.

(* Axiom that allows us to cast any type to any type *)
Axiom unsafe_cast : forall {A B : Type}, A -> B.

(* Axiom of choice-like function *)
Axiom choose : forall {A : Type} (P : A -> Prop), (exists x, P x) -> A.

(* Excluded middle for any Prop *)
Axiom excluded_middle : forall P : Prop, P \/ ~P.

Record Rec := mkRec {
  f1 : nat;
  f2 : nat
}.

(* Try to confuse extraction with unsafe casts *)
Definition cast_confusion (r : Rec) : nat :=
  match r with
  | mkRec a b =>
      (* Cast the field to itself via any *)
      unsafe_cast a + b
  end.

(* Use choose in record match *)
Axiom nat_gt_0_witness : 1 > 0.

Definition choose_in_match (r : Rec) : nat :=
  match r with
  | mkRec a b =>
      let witness := choose (fun n => n > 0) (ex_intro (fun n => n > 0) 1 nat_gt_0_witness) in
      a + b + witness
  end.

(* Record with Prop fields that have computational content via axioms *)
Record ProofRec := mkProofRec {
  pf_val : nat;
  pf_proof : pf_val > 0;
  pf_val2 : nat
}.

Definition extract_proof_computation (pr : ProofRec) : nat :=
  match pr with
  | mkProofRec v p v2 =>
      (* Access record with Prop field in match *)
      v + v2
  end.

(* Axiom that claims equality of different types *)
Axiom type_equality : nat = bool.

(* Try to use this bad axiom *)
Definition use_type_eq (n : nat) : bool :=
  match type_equality in (_ = T) return T with
  | eq_refl => n
  end.

(* Use axiom to create "impossible" record *)
Axiom impossible_rec : Rec.

Definition use_impossible (_ : unit) : nat :=
  match impossible_rec with
  | mkRec a b => a + b
  end.

(* Axiom claiming False *)
Axiom false_axiom : False.

Definition from_false (r : Rec) : nat :=
  match r with
  | mkRec a b =>
      match false_axiom with end
  end.

(* Prop that extracts to unit but use it computationally *)
Definition prop_computation (r : Rec) : Prop :=
  match r with
  | mkRec a b => a + b = 0
  end.

(* Extract Prop as if it were Type *)
Axiom prop_as_type : forall (P : Prop), P -> nat.

Definition use_prop_as_type (r : Rec) (prf : 0 = 0) : nat :=
  match r with
  | mkRec a b =>
      (* Use axiom to extract nat from Prop *)
      prop_as_type _ prf + a + b
  end.

End UnsoundAxioms.

Crane Extraction "unsound_axioms" UnsoundAxioms.
