(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: validated virtual crossmatch, complement-fixing DSA, and safe release order creation. *)

From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

Module ValidatedVirtualCrossmatchTraceCase.

Inductive HLALocus : Type :=
| Locus_A
| Locus_B
| Locus_DR.

Definition hla_locus_eq_dec (x y : HLALocus) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Record HLAAllele : Type := mkHLAAllele {
  hla_locus : HLALocus;
  hla_group : nat
}.

Definition hla_allele_eq_dec (x y : HLAAllele) : {x = y} + {x <> y}.
Proof.
  decide equality.
  - apply Nat.eq_dec.
  - apply hla_locus_eq_dec.
Defined.

Definition hla_allele_eqb (x y : HLAAllele) : bool :=
  if hla_allele_eq_dec x y then true else false.

Record HLATyping : Type := mkHLATyping {
  hla_typed_alleles : list HLAAllele
}.

Record HLAEpitope : Type := mkHLAEpitope {
  epitope_id : nat;
  epitope_locus : HLALocus;
  epitope_immunogenic : bool
}.

Definition epitope_eq_dec (x y : HLAEpitope) : {x = y} + {x <> y}.
Proof.
  decide equality.
  - apply Bool.bool_dec.
  - apply hla_locus_eq_dec.
  - apply Nat.eq_dec.
Defined.

Definition epitope_eqb (x y : HLAEpitope) : bool :=
  if epitope_eq_dec x y then true else false.

Definition eplet_62GE : HLAEpitope := mkHLAEpitope 62 Locus_A true.
Definition eplet_65QIA : HLAEpitope := mkHLAEpitope 65 Locus_A true.
Definition eplet_142T : HLAEpitope := mkHLAEpitope 142 Locus_B true.
Definition eplet_77N : HLAEpitope := mkHLAEpitope 77 Locus_DR true.

Definition allele_epitopes (a : HLAAllele) : list HLAEpitope :=
  match hla_locus a, hla_group a with
  | Locus_A, 2 => [eplet_62GE; eplet_65QIA]
  | Locus_A, 3 => [eplet_62GE]
  | Locus_B, 7 => [eplet_142T]
  | Locus_DR, 4 => [eplet_77N]
  | _, _ => []
  end.

Definition typing_epitopes (t : HLATyping) : list HLAEpitope :=
  flat_map allele_epitopes (hla_typed_alleles t).

Fixpoint epitope_dedup (l : list HLAEpitope) : list HLAEpitope :=
  match l with
  | [] => []
  | x :: xs =>
      if existsb (epitope_eqb x) xs then epitope_dedup xs
      else x :: epitope_dedup xs
  end.

Record EpitopeAntibody : Type := mkEpitopeAntibody {
  ab_epitope : HLAEpitope;
  ab_mfi : nat;
  ab_complement_fixing : bool
}.

Record VirtualXMProfile : Type := mkVirtualXMProfile {
  vxm_epitope_abs : list EpitopeAntibody;
  vxm_current_pra : nat;
  vxm_peak_pra : nat;
  vxm_sensitization_events : nat
}.

Record MFIThresholdConfig : Type := mkMFIThresholdConfig {
  mfi_cfg_negative : nat;
  mfi_cfg_weak_positive : nat;
  mfi_cfg_moderate : nat;
  mfi_cfg_strong : nat;
  mfi_cfg_lab_id : nat;
  mfi_cfg_validated : bool
}.

Definition mfi_config_valid (cfg : MFIThresholdConfig) : bool :=
  Nat.ltb (mfi_cfg_negative cfg) (mfi_cfg_weak_positive cfg) &&
  Nat.ltb (mfi_cfg_weak_positive cfg) (mfi_cfg_moderate cfg) &&
  Nat.ltb (mfi_cfg_moderate cfg) (mfi_cfg_strong cfg).

Definition example_luminex_thresholds : MFIThresholdConfig :=
  mkMFIThresholdConfig 1000 3000 8000 12000 1 true.

Lemma luminex_thresholds_valid :
  mfi_config_valid example_luminex_thresholds = true.
Proof. reflexivity. Qed.

Lemma luminex_validated_proof :
  mfi_cfg_validated example_luminex_thresholds = true.
Proof. reflexivity. Qed.

Record ValidatedMFIConfig : Type := mkValidatedMFIConfig {
  vmc_config : MFIThresholdConfig;
  vmc_valid : mfi_config_valid vmc_config = true;
  vmc_lab_validated : mfi_cfg_validated vmc_config = true
}.

Definition validated_luminex : ValidatedMFIConfig :=
  mkValidatedMFIConfig
    example_luminex_thresholds
    luminex_thresholds_valid
    luminex_validated_proof.

Inductive MFIStrength : Type :=
| MFI_Negative
| MFI_WeakPositive
| MFI_Moderate
| MFI_Strong
| MFI_VeryStrong.

Definition classify_mfi_with_config (cfg : MFIThresholdConfig) (mfi : nat) : MFIStrength :=
  if Nat.leb mfi (mfi_cfg_negative cfg) then MFI_Negative
  else if Nat.leb mfi (mfi_cfg_weak_positive cfg) then MFI_WeakPositive
  else if Nat.leb mfi (mfi_cfg_moderate cfg) then MFI_Moderate
  else if Nat.leb mfi (mfi_cfg_strong cfg) then MFI_Strong
  else MFI_VeryStrong.

Definition classify_mfi_safe (vcfg : ValidatedMFIConfig) (mfi : nat) : MFIStrength :=
  classify_mfi_with_config (vmc_config vcfg) mfi.

Theorem all_validated_configs_zero_negative :
  forall (vcfg : ValidatedMFIConfig),
    classify_mfi_safe vcfg 0 = MFI_Negative.
Proof.
  intro vcfg.
  unfold classify_mfi_safe, classify_mfi_with_config.
  destruct (Nat.leb 0 (mfi_cfg_negative (vmc_config vcfg))) eqn:H.
  - reflexivity.
  - apply Nat.leb_nle in H. lia.
Qed.

Definition mfi_negative_threshold : nat := 1000.

Definition max_dsa_mfi (recipient : VirtualXMProfile) (donor : HLATyping) : nat :=
  let donor_epitopes := epitope_dedup (typing_epitopes donor) in
  fold_left
    (fun acc ab =>
      if existsb (epitope_eqb (ab_epitope ab)) donor_epitopes
      then Nat.max acc (ab_mfi ab)
      else acc)
    (vxm_epitope_abs recipient)
    0.

Definition has_complement_fixing_dsa (recipient : VirtualXMProfile) (donor : HLATyping) : bool :=
  let donor_epitopes := epitope_dedup (typing_epitopes donor) in
  existsb
    (fun ab =>
      ab_complement_fixing ab &&
      Nat.ltb mfi_negative_threshold (ab_mfi ab) &&
      existsb (epitope_eqb (ab_epitope ab)) donor_epitopes)
    (vxm_epitope_abs recipient).

Inductive VirtualXMResult : Type :=
| VXM_Negative
| VXM_WeakPositive
| VXM_Positive
| VXM_StrongPositive.

Definition virtual_crossmatch_safe
    (vcfg : ValidatedMFIConfig)
    (recipient : VirtualXMProfile)
    (donor : HLATyping)
    : VirtualXMResult :=
  let max_mfi := max_dsa_mfi recipient donor in
  match classify_mfi_safe vcfg max_mfi with
  | MFI_Negative => VXM_Negative
  | MFI_WeakPositive => VXM_WeakPositive
  | MFI_Moderate => VXM_Positive
  | MFI_Strong => VXM_StrongPositive
  | MFI_VeryStrong => VXM_StrongPositive
  end.

Inductive TransplantAcceptability : Type :=
| Acceptable
| Acceptable_With_Desensitization
| Unacceptable_High_Risk
| Absolute_Contraindication.

Definition transplant_acceptability
    (vxm : VirtualXMResult)
    (complement_fixing_dsa : bool)
    : TransplantAcceptability :=
  match vxm, complement_fixing_dsa with
  | VXM_Negative, _ => Acceptable
  | VXM_WeakPositive, false => Acceptable_With_Desensitization
  | VXM_WeakPositive, true => Unacceptable_High_Risk
  | VXM_Positive, _ => Unacceptable_High_Risk
  | VXM_StrongPositive, _ => Absolute_Contraindication
  end.

Definition full_virtual_crossmatch_safe
    (vcfg : ValidatedMFIConfig)
    (recipient : VirtualXMProfile)
    (donor : HLATyping)
    : TransplantAcceptability :=
  let vxm := virtual_crossmatch_safe vcfg recipient donor in
  let cf := has_complement_fixing_dsa recipient donor in
  transplant_acceptability vxm cf.

Inductive TestConfidence : Type :=
| Confidence_High
| Confidence_Medium
| Confidence_Low.

Inductive CrossmatchResult : Type :=
| XM_Compatible
| XM_Incompatible
| XM_Inconclusive
| XM_Not_Done.

Record CrossmatchWithUncertainty := mkCrossmatchWithUncertainty {
  xmu_result : CrossmatchResult;
  xmu_method : nat;
  xmu_confidence : TestConfidence
}.

Definition safe_to_release (xm : CrossmatchWithUncertainty) : bool :=
  match xmu_result xm, xmu_confidence xm with
  | XM_Compatible, Confidence_High => true
  | XM_Compatible, Confidence_Medium => true
  | _, _ => false
  end.

Record SafeTransfusionOrder := mkSafeTransfusionOrder {
  sto_recipient_id : nat;
  sto_product_id : nat;
  sto_compatibility_check : bool;
  sto_crossmatch : CrossmatchWithUncertainty;
  sto_sample_collection_time : nat;
  sto_authorized_by : nat;
  sto_emergency_release : bool
}.

Definition order_sample_valid (collection_time current_time : nat) : bool :=
  Nat.leb (current_time - collection_time) (72 * 3600).

Definition transfusion_order_authorized
    (order : SafeTransfusionOrder)
    (current_time : nat)
    : bool :=
  let compat_ok := sto_compatibility_check order in
  let xm_ok := safe_to_release (sto_crossmatch order) in
  let sample_ok := order_sample_valid (sto_sample_collection_time order) current_time in
  let emergency := sto_emergency_release order in
  (compat_ok && xm_ok && sample_ok) || emergency.

Definition create_safe_transfusion_order
    (recipient_id product_id : nat)
    (compat_result : bool)
    (xm : CrossmatchWithUncertainty)
    (sample_time current_time : nat)
    (authorizer : nat)
    (is_emergency : bool)
    : option SafeTransfusionOrder :=
  let order := mkSafeTransfusionOrder
                 recipient_id product_id compat_result xm
                 sample_time authorizer is_emergency in
  if transfusion_order_authorized order current_time then Some order else None.

Definition donor_hla : HLATyping :=
  mkHLATyping
    [mkHLAAllele Locus_A 2;
     mkHLAAllele Locus_A 3;
     mkHLAAllele Locus_B 7;
     mkHLAAllele Locus_DR 4].

Definition weak_profile : VirtualXMProfile :=
  mkVirtualXMProfile
    [mkEpitopeAntibody eplet_65QIA 2500 false;
     mkEpitopeAntibody eplet_77N 800 false]
    32 40 2.

Definition strong_profile : VirtualXMProfile :=
  mkVirtualXMProfile
    [mkEpitopeAntibody eplet_65QIA 9000 true;
     mkEpitopeAntibody eplet_142T 6000 false]
    95 98 5.

Definition good_crossmatch : CrossmatchWithUncertainty :=
  mkCrossmatchWithUncertainty XM_Compatible 1 Confidence_High.

Definition bad_crossmatch : CrossmatchWithUncertainty :=
  mkCrossmatchWithUncertainty XM_Incompatible 1 Confidence_High.

Definition risk_acceptable (a : TransplantAcceptability) : bool :=
  match a with
  | Acceptable => true
  | Acceptable_With_Desensitization => true
  | _ => false
  end.

Definition sample_virtual_zero_negative : bool :=
  match classify_mfi_safe validated_luminex 0 with
  | MFI_Negative => true
  | _ => false
  end.

Definition sample_dedup_count : nat :=
  length (epitope_dedup (typing_epitopes donor_hla)).

Definition sample_weak_acceptability : bool :=
  match full_virtual_crossmatch_safe validated_luminex weak_profile donor_hla with
  | Acceptable_With_Desensitization => true
  | _ => false
  end.

Definition sample_strong_absolute_contra : bool :=
  match full_virtual_crossmatch_safe validated_luminex strong_profile donor_hla with
  | Absolute_Contraindication => true
  | _ => false
  end.

Definition sample_strong_has_complement_fixing_dsa : bool :=
  has_complement_fixing_dsa strong_profile donor_hla.

Definition sample_strong_max_mfi : nat :=
  max_dsa_mfi strong_profile donor_hla.

Definition sample_lab_id : nat :=
  mfi_cfg_lab_id (vmc_config validated_luminex).

Definition sample_order_created : bool :=
  match create_safe_transfusion_order
          100 200
          (risk_acceptable (full_virtual_crossmatch_safe validated_luminex weak_profile donor_hla))
          good_crossmatch
          0 1000 77 false with
  | Some _ => true
  | None => false
  end.

Definition sample_order_blocked : bool :=
  match create_safe_transfusion_order
          100 201
          (risk_acceptable (full_virtual_crossmatch_safe validated_luminex strong_profile donor_hla))
          bad_crossmatch
          0 1000 77 false with
  | Some _ => false
  | None => true
  end.

Definition sample_authorized_order_stays_authorized : bool :=
  match create_safe_transfusion_order
          100 202
          true
          good_crossmatch
          100 200 88 false with
  | Some order => transfusion_order_authorized order 200
  | None => false
  end.

End ValidatedVirtualCrossmatchTraceCase.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "validated_virtual_crossmatch_trace" ValidatedVirtualCrossmatchTraceCase.
