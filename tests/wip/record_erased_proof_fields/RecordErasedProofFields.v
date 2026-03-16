(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: records with surviving data fields and erased proof fields. *)

From Stdlib Require Import List.
Import ListNotations.

Module RecordErasedProofFieldsCase.

Inductive ItemKind : Type :=
| KindA
| KindB
| KindC
| KindD
| KindE
| KindF
| KindG.

Inductive StoredTag : Type :=
| TagPrimary : ItemKind -> StoredTag
| TagSecondary : ItemKind -> StoredTag.

Inductive TraceBucket : Type :=
| BucketA
| BucketB
| BucketC.

Record PrimaryRecord : Type := mkPrimaryRecord {
  primary_left_kind : ItemKind;
  primary_right_kind : ItemKind;
  primary_left_is_target : primary_left_kind = KindC;
  primary_right_is_target : primary_right_kind = KindE;
  primary_tag : StoredTag;
  primary_reflexive_proof : forall k : ItemKind, k = k
}.

Record ErasedProofRecord : Type := mkErasedProofRecord {
  erased_bucket : TraceBucket;
  erased_predicate : ItemKind -> Prop;
  erased_flag : Prop
}.

Definition kind_code (k : ItemKind) : nat :=
  match k with
  | KindA => 0
  | KindB => 1
  | KindC => 2
  | KindD => 3
  | KindE => 4
  | KindF => 5
  | KindG => 6
  end.

Definition tag_code (t : StoredTag) : nat :=
  match t with
  | TagPrimary k => 10 + kind_code k
  | TagSecondary k => 20 + kind_code k
  end.

Definition bucket_code (b : TraceBucket) : nat :=
  match b with
  | BucketA => 30
  | BucketB => 31
  | BucketC => 32
  end.

Definition bucket_to_tag (b : TraceBucket) : StoredTag :=
  match b with
  | BucketA => TagSecondary KindD
  | BucketB => TagSecondary KindE
  | BucketC => TagSecondary KindB
  end.

Definition sample_primary_record : PrimaryRecord :=
  mkPrimaryRecord
    KindC
    KindE
    eq_refl
    eq_refl
    (TagPrimary KindC)
    (fun _ => eq_refl).

Definition sample_erased_proof_record : ErasedProofRecord :=
  mkErasedProofRecord
    BucketC
    (fun _ => True)
    True.

Definition left_kind_code_of (r : PrimaryRecord) : nat :=
  kind_code (primary_left_kind r).

Definition right_kind_code_of (r : PrimaryRecord) : nat :=
  kind_code (primary_right_kind r).

Definition tag_code_of (r : PrimaryRecord) : nat :=
  tag_code (primary_tag r).

Definition bucket_code_of (r : ErasedProofRecord) : nat :=
  bucket_code (erased_bucket r).

Definition trace_codes_of
    (primary : PrimaryRecord)
    (erased : ErasedProofRecord)
    : list nat :=
  [ left_kind_code_of primary;
    right_kind_code_of primary;
    tag_code_of primary;
    bucket_code_of erased;
    tag_code (bucket_to_tag (erased_bucket erased)) ].

Definition trace_checksum_of
    (primary : PrimaryRecord)
    (erased : ErasedProofRecord)
    : nat :=
  fold_left Nat.add (trace_codes_of primary erased) 0.

Definition sample_left_kind_code : nat :=
  left_kind_code_of sample_primary_record.

Definition sample_right_kind_code : nat :=
  right_kind_code_of sample_primary_record.

Definition sample_tag_code : nat :=
  tag_code_of sample_primary_record.

Definition sample_bucket_code : nat :=
  bucket_code_of sample_erased_proof_record.

Definition sample_trace_checksum : nat :=
  trace_checksum_of sample_primary_record sample_erased_proof_record.

End RecordErasedProofFieldsCase.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "record_erased_proof_fields" RecordErasedProofFieldsCase.
