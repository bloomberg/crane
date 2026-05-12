(* Regression: sigT constructor with dependent second component.
   When the first and second ML type parameters of sigT resolve to
   the same base type (e.g., both are Label_), the second template
   parameter must be std::any because the actual type varies per
   constructor branch.  Previously Crane emitted SigT<Label_, Label_>
   which caused type mismatches when the second component was unit or
   nat instead of Label_. *)

From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import Specif.

Inductive tag := TagA | TagB | TagC.

Definition tag_type (t : tag) : Type :=
  match t with
  | TagA => unit
  | TagB => nat
  | TagC => bool
  end.

Module Packer.

  Definition pack_a : {t : tag & tag_type t} :=
    existT tag_type TagA tt.

  Definition pack_b (n : nat) : {t : tag & tag_type t} :=
    existT tag_type TagB n.

  Definition pack_c (b : bool) : {t : tag & tag_type t} :=
    existT tag_type TagC b.

  Definition get_tag (p : {t : tag & tag_type t}) : tag :=
    projT1 p.

End Packer.

Crane Extraction "sep_ext_sigt_dependent" Packer.
