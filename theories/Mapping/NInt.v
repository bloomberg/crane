(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Extraction of [positive] and [N] to [unsigned int], std flavour: the mappings of [Mapping.NIntDefs]. *)
From Crane Require Extraction.
From Crane Require Export Mapping.Std.
From Crane Require Import Mapping.Descriptor Mapping.Cpp Mapping.NIntDefs.
From Stdlib Require Import BinNat BinPos BinInt.

(** [positive] is an [unsigned int], matched by parity. *)
#[export] Instance std_positive_mapping : TypeMapping positive := positive_mapping.
(** [N] is an [unsigned int]. *)
#[export] Instance std_n_mapping : TypeMapping N := n_mapping.
(** [Pos.add] is [+]; wraps at 2^32. *)
#[export] Instance std_pos_add_mapping : OperationMapping (Ref Pos.add) := pos_add_mapping.
(** [Pos.sub] is [-], floored at [1]. *)
#[export] Instance std_pos_sub_mapping : OperationMapping (Ref Pos.sub) := pos_sub_mapping.
(** [Pos.mul] is [*]; wraps at 2^32. *)
#[export] Instance std_pos_mul_mapping : OperationMapping (Ref Pos.mul) := pos_mul_mapping.
(** [Pos.succ] is [x + 1]; wraps at 2^32. *)
#[export] Instance std_pos_succ_mapping : OperationMapping (Ref Pos.succ) := pos_succ_mapping.
(** [Pos.pred] is [x - 1], floored at [1]. *)
#[export] Instance std_pos_pred_mapping : OperationMapping (Ref Pos.pred) := pos_pred_mapping.
(** [Pos.eqb] is [==]. *)
#[export] Instance std_pos_eqb_mapping : OperationMapping (Ref Pos.eqb) := pos_eqb_mapping.
(** [Pos.ltb] is [<]. *)
#[export] Instance std_pos_ltb_mapping : OperationMapping (Ref Pos.ltb) := pos_ltb_mapping.
(** [Pos.leb] is [<=]. *)
#[export] Instance std_pos_leb_mapping : OperationMapping (Ref Pos.leb) := pos_leb_mapping.
(** [Pos.compare] is a three-way test on [<]. *)
#[export] Instance std_pos_compare_mapping : OperationMapping (Ref Pos.compare) := pos_compare_mapping.
(** [Pos.eq_dec] is [==]. *)
#[export] Instance std_pos_eq_dec_mapping : OperationMapping (Ref Pos.eq_dec) := pos_eq_dec_mapping.
(** [Pos.min] is [std::min]. *)
#[export] Instance std_pos_min_mapping : OperationMapping (Ref Pos.min) := pos_min_mapping std_flavour.
(** [Pos.max] is [std::max]. *)
#[export] Instance std_pos_max_mapping : OperationMapping (Ref Pos.max) := pos_max_mapping std_flavour.
(** [N.add] is [+]; wraps at 2^32. *)
#[export] Instance std_n_add_mapping : OperationMapping (Ref N.add) := n_add_mapping.
(** [N.sub] is [-], floored at [0]. *)
#[export] Instance std_n_sub_mapping : OperationMapping (Ref N.sub) := n_sub_mapping.
(** [N.mul] is [*]; wraps at 2^32. *)
#[export] Instance std_n_mul_mapping : OperationMapping (Ref N.mul) := n_mul_mapping.
(** [N.div] is [/], [0] for a zero divisor. *)
#[export] Instance std_n_div_mapping : OperationMapping (Ref N.div) := n_div_mapping.
(** [N.modulo] is [%], [a] for a zero divisor. *)
#[export] Instance std_n_modulo_mapping : OperationMapping (Ref N.modulo) := n_modulo_mapping.
(** [N.succ] is [n + 1]; wraps at 2^32. *)
#[export] Instance std_n_succ_mapping : OperationMapping (Ref N.succ) := n_succ_mapping.
(** [N.pred] is [n - 1], floored at [0]. *)
#[export] Instance std_n_pred_mapping : OperationMapping (Ref N.pred) := n_pred_mapping.
(** [N.eqb] is [==]. *)
#[export] Instance std_n_eqb_mapping : OperationMapping (Ref N.eqb) := n_eqb_mapping.
(** [N.ltb] is [<]. *)
#[export] Instance std_n_ltb_mapping : OperationMapping (Ref N.ltb) := n_ltb_mapping.
(** [N.leb] is [<=]. *)
#[export] Instance std_n_leb_mapping : OperationMapping (Ref N.leb) := n_leb_mapping.
(** [N.compare] is a three-way test on [<]. *)
#[export] Instance std_n_compare_mapping : OperationMapping (Ref N.compare) := n_compare_mapping.
(** [N.eq_dec] is [==]. *)
#[export] Instance std_n_eq_dec_mapping : OperationMapping (Ref N.eq_dec) := n_eq_dec_mapping.
(** [N.min] is [std::min]. *)
#[export] Instance std_n_min_mapping : OperationMapping (Ref N.min) := n_min_mapping std_flavour.
(** [N.max] is [std::max]. *)
#[export] Instance std_n_max_mapping : OperationMapping (Ref N.max) := n_max_mapping std_flavour.
(** [N.double] is [n * 2]; wraps at 2^32. *)
#[export] Instance std_n_double_mapping : OperationMapping (Ref N.double) := n_double_mapping.
(** [N.succ_double] is [x * 2 + 1]; wraps at 2^32. *)
#[export] Instance std_n_succ_double_mapping : OperationMapping (Ref N.succ_double) := n_succ_double_mapping.
(** [N.of_nat] wraps the [nat] into [unsigned int]. *)
#[export] Instance std_n_of_nat_mapping : OperationMapping (Ref N.of_nat) := n_of_nat_mapping.
(** [N.to_nat] is an exact cast to the [nat] type. *)
#[export] Instance std_n_to_nat_mapping : OperationMapping (Ref N.to_nat) := n_to_nat_mapping.
(** [Pos.of_nat] sends [0] to [1], otherwise casts. *)
#[export] Instance std_pos_of_nat_mapping : OperationMapping (Ref Pos.of_nat) := pos_of_nat_mapping.
(** [Pos.to_nat] is an exact cast to the [nat] type. *)
#[export] Instance std_pos_to_nat_mapping : OperationMapping (Ref Pos.to_nat) := pos_to_nat_mapping.
