(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Extraction of [positive] and [N] to [unsigned int], std flavour: the mappings of [Mapping.NIntDefs]. *)
From Crane Require Extraction.
From Crane Require Export Mapping.Std.
From Crane Require Import Mapping.Descriptor Mapping.Cpp Mapping.NIntDefs.
From Stdlib Require Import BinNat BinPos BinInt.

#[export] Instance std_positive_mapping : TypeMapping positive := positive_mapping.
#[export] Instance std_n_mapping : TypeMapping N := n_mapping.
#[export] Instance std_pos_add_mapping : OperationMapping (Ref Pos.add) := pos_add_mapping.
#[export] Instance std_pos_sub_mapping : OperationMapping (Ref Pos.sub) := pos_sub_mapping.
#[export] Instance std_pos_mul_mapping : OperationMapping (Ref Pos.mul) := pos_mul_mapping.
#[export] Instance std_pos_succ_mapping : OperationMapping (Ref Pos.succ) := pos_succ_mapping.
#[export] Instance std_pos_pred_mapping : OperationMapping (Ref Pos.pred) := pos_pred_mapping.
#[export] Instance std_pos_eqb_mapping : OperationMapping (Ref Pos.eqb) := pos_eqb_mapping.
#[export] Instance std_pos_ltb_mapping : OperationMapping (Ref Pos.ltb) := pos_ltb_mapping.
#[export] Instance std_pos_leb_mapping : OperationMapping (Ref Pos.leb) := pos_leb_mapping.
#[export] Instance std_pos_compare_mapping : OperationMapping (Ref Pos.compare) := pos_compare_mapping.
#[export] Instance std_pos_eq_dec_mapping : OperationMapping (Ref Pos.eq_dec) := pos_eq_dec_mapping.
#[export] Instance std_pos_min_mapping : OperationMapping (Ref Pos.min) := pos_min_mapping std_flavour.
#[export] Instance std_pos_max_mapping : OperationMapping (Ref Pos.max) := pos_max_mapping std_flavour.
#[export] Instance std_n_add_mapping : OperationMapping (Ref N.add) := n_add_mapping.
#[export] Instance std_n_sub_mapping : OperationMapping (Ref N.sub) := n_sub_mapping.
#[export] Instance std_n_mul_mapping : OperationMapping (Ref N.mul) := n_mul_mapping.
#[export] Instance std_n_div_mapping : OperationMapping (Ref N.div) := n_div_mapping.
#[export] Instance std_n_modulo_mapping : OperationMapping (Ref N.modulo) := n_modulo_mapping.
#[export] Instance std_n_succ_mapping : OperationMapping (Ref N.succ) := n_succ_mapping.
#[export] Instance std_n_pred_mapping : OperationMapping (Ref N.pred) := n_pred_mapping.
#[export] Instance std_n_eqb_mapping : OperationMapping (Ref N.eqb) := n_eqb_mapping.
#[export] Instance std_n_ltb_mapping : OperationMapping (Ref N.ltb) := n_ltb_mapping.
#[export] Instance std_n_leb_mapping : OperationMapping (Ref N.leb) := n_leb_mapping.
#[export] Instance std_n_compare_mapping : OperationMapping (Ref N.compare) := n_compare_mapping.
#[export] Instance std_n_eq_dec_mapping : OperationMapping (Ref N.eq_dec) := n_eq_dec_mapping.
#[export] Instance std_n_min_mapping : OperationMapping (Ref N.min) := n_min_mapping std_flavour.
#[export] Instance std_n_max_mapping : OperationMapping (Ref N.max) := n_max_mapping std_flavour.
#[export] Instance std_n_double_mapping : OperationMapping (Ref N.double) := n_double_mapping.
#[export] Instance std_n_succ_double_mapping : OperationMapping (Ref N.succ_double) := n_succ_double_mapping.
#[export] Instance std_n_of_nat_mapping : OperationMapping (Ref N.of_nat) := n_of_nat_mapping.
#[export] Instance std_n_to_nat_mapping : OperationMapping (Ref N.to_nat) := n_to_nat_mapping.
#[export] Instance std_pos_of_nat_mapping : OperationMapping (Ref Pos.of_nat) := pos_of_nat_mapping.
#[export] Instance std_pos_to_nat_mapping : OperationMapping (Ref Pos.to_nat) := pos_to_nat_mapping.
