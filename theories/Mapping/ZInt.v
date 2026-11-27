(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Extraction of [Z] to [int64_t], std flavour: the mappings of [Mapping.ZIntDefs]. *)
From Crane Require Extraction.
From Crane Require Export Mapping.NInt Mapping.NatInt.
From Crane Require Import Mapping.Descriptor Mapping.Cpp Mapping.ZIntDefs.
From Stdlib Require Import BinNat BinPos BinInt.

#[export] Instance std_z_mapping : TypeMapping Z := z_mapping.
#[export] Instance std_z_add_mapping : OperationMapping (Ref Z.add) := z_add_mapping.
#[export] Instance std_z_sub_mapping : OperationMapping (Ref Z.sub) := z_sub_mapping.
#[export] Instance std_z_mul_mapping : OperationMapping (Ref Z.mul) := z_mul_mapping.
#[export] Instance std_z_div_mapping : OperationMapping (Ref Z.div) := z_div_mapping.
#[export] Instance std_z_modulo_mapping : OperationMapping (Ref Z.modulo) := z_modulo_mapping.
#[export] Instance std_z_opp_mapping : OperationMapping (Ref Z.opp) := z_opp_mapping.
#[export] Instance std_z_abs_mapping : OperationMapping (Ref Z.abs) := z_abs_mapping.
#[export] Instance std_z_succ_mapping : OperationMapping (Ref Z.succ) := z_succ_mapping.
#[export] Instance std_z_pred_mapping : OperationMapping (Ref Z.pred) := z_pred_mapping.
#[export] Instance std_z_eqb_mapping : OperationMapping (Ref Z.eqb) := z_eqb_mapping.
#[export] Instance std_z_ltb_mapping : OperationMapping (Ref Z.ltb) := z_ltb_mapping.
#[export] Instance std_z_leb_mapping : OperationMapping (Ref Z.leb) := z_leb_mapping.
#[export] Instance std_z_gtb_mapping : OperationMapping (Ref Z.gtb) := z_gtb_mapping.
#[export] Instance std_z_geb_mapping : OperationMapping (Ref Z.geb) := z_geb_mapping.
#[export] Instance std_z_compare_mapping : OperationMapping (Ref Z.compare) := z_compare_mapping.
#[export] Instance std_z_eq_dec_mapping : OperationMapping (Ref Z.eq_dec) := z_eq_dec_mapping.
#[export] Instance std_z_min_mapping : OperationMapping (Ref Z.min) := z_min_mapping std_flavour.
#[export] Instance std_z_max_mapping : OperationMapping (Ref Z.max) := z_max_mapping std_flavour.
#[export] Instance std_z_of_nat_mapping : OperationMapping (Ref Z.of_nat) := z_of_nat_mapping.
#[export] Instance std_z_to_nat_mapping : OperationMapping (Ref Z.to_nat) := z_to_nat_mapping.
#[export] Instance std_z_of_N_mapping : OperationMapping (Ref Z.of_N) := z_of_N_mapping.
#[export] Instance std_z_to_N_mapping : OperationMapping (Ref Z.to_N) := z_to_N_mapping.
#[export] Instance std_z_abs_N_mapping : OperationMapping (Ref Z.abs_N) := z_abs_N_mapping.
