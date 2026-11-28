(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Extraction of [Z] to [int64_t], BDE flavour: the mappings of [Mapping.ZIntDefs]. *)
From Crane Require Extraction.
From Crane Require Export Mapping.NIntBDE Mapping.NatIntBDE.
From Crane Require Import Mapping.Descriptor Mapping.Cpp Mapping.ZIntDefs.
From Stdlib Require Import BinNat BinPos BinInt.

(** [Z] is an [int64_t]. *)
#[export] Instance bde_z_mapping : TypeMapping Z := z_mapping.
(** [Z.add] is [+], wrapping modulo 2^64. *)
#[export] Instance bde_z_add_mapping : OperationMapping (Ref Z.add) := z_add_mapping.
(** [Z.sub] is [-], wrapping modulo 2^64. *)
#[export] Instance bde_z_sub_mapping : OperationMapping (Ref Z.sub) := z_sub_mapping.
(** [Z.mul] is [*], wrapping modulo 2^64. *)
#[export] Instance bde_z_mul_mapping : OperationMapping (Ref Z.mul) := z_mul_mapping.
(** [Z.div] is floored division, [0] for a zero divisor. *)
#[export] Instance bde_z_div_mapping : OperationMapping (Ref Z.div) := z_div_mapping.
(** [Z.modulo] is the floored remainder, [a] for a zero divisor. *)
#[export] Instance bde_z_modulo_mapping : OperationMapping (Ref Z.modulo) := z_modulo_mapping.
(** [Z.opp] is wrapping negation. *)
#[export] Instance bde_z_opp_mapping : OperationMapping (Ref Z.opp) := z_opp_mapping.
(** [Z.abs] is wrapping absolute value. *)
#[export] Instance bde_z_abs_mapping : OperationMapping (Ref Z.abs) := z_abs_mapping.
(** [Z.succ] is wrapping [x + 1]. *)
#[export] Instance bde_z_succ_mapping : OperationMapping (Ref Z.succ) := z_succ_mapping.
(** [Z.pred] is wrapping [x - 1]. *)
#[export] Instance bde_z_pred_mapping : OperationMapping (Ref Z.pred) := z_pred_mapping.
(** [Z.eqb] is [==]. *)
#[export] Instance bde_z_eqb_mapping : OperationMapping (Ref Z.eqb) := z_eqb_mapping.
(** [Z.ltb] is [<]. *)
#[export] Instance bde_z_ltb_mapping : OperationMapping (Ref Z.ltb) := z_ltb_mapping.
(** [Z.leb] is [<=]. *)
#[export] Instance bde_z_leb_mapping : OperationMapping (Ref Z.leb) := z_leb_mapping.
(** [Z.gtb] is [>]. *)
#[export] Instance bde_z_gtb_mapping : OperationMapping (Ref Z.gtb) := z_gtb_mapping.
(** [Z.geb] is [>=]. *)
#[export] Instance bde_z_geb_mapping : OperationMapping (Ref Z.geb) := z_geb_mapping.
(** [Z.compare] is a three-way test on [<]. *)
#[export] Instance bde_z_compare_mapping : OperationMapping (Ref Z.compare) := z_compare_mapping.
(** [Z.eq_dec] is [==]. *)
#[export] Instance bde_z_eq_dec_mapping : OperationMapping (Ref Z.eq_dec) := z_eq_dec_mapping.
(** [Z.min] is [bsl::min]. *)
#[export] Instance bde_z_min_mapping : OperationMapping (Ref Z.min) := z_min_mapping bde_flavour.
(** [Z.max] is [bsl::max]. *)
#[export] Instance bde_z_max_mapping : OperationMapping (Ref Z.max) := z_max_mapping bde_flavour.
(** [Z.of_nat] widens the [unsigned int]. *)
#[export] Instance bde_z_of_nat_mapping : OperationMapping (Ref Z.of_nat) := z_of_nat_mapping.
(** [Z.to_nat] clamps negatives to [0], then wraps into [unsigned int]. *)
#[export] Instance bde_z_to_nat_mapping : OperationMapping (Ref Z.to_nat) := z_to_nat_mapping.
(** [Z.of_N] widens the [unsigned int]. *)
#[export] Instance bde_z_of_N_mapping : OperationMapping (Ref Z.of_N) := z_of_N_mapping.
(** [Z.to_N] clamps negatives to [0], then wraps into [unsigned int]. *)
#[export] Instance bde_z_to_N_mapping : OperationMapping (Ref Z.to_N) := z_to_N_mapping.
(** [Z.abs_N] is the magnitude, wrapped into [unsigned int]. *)
#[export] Instance bde_z_abs_N_mapping : OperationMapping (Ref Z.abs_N) := z_abs_N_mapping.
