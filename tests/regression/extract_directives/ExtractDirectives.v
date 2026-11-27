(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Opaque vs transparent definitions and their effect on extraction. *)
(* Standard Coq extraction directives (Extract Inductive, Extraction Inline) *)
(* are OCaml-only and not recognized by Rocq 9.0 / Crane. *)
(* This test focuses on Qed vs Defined opacity and Section variables. *)

From Stdlib Require Import List Nat Bool Arith Lia.
Import ListNotations.

Module ExtractDirectives.

(* Section with local variables — tests extraction of section-abstracted defs *)
Section WithBase.
  Variable base : nat.

  Definition offset (x : nat) : nat := x + base.
  Definition scale (x : nat) : nat := x * base.
  Definition transform (x : nat) : nat := scale (offset x).
End WithBase.

(* After closing section, offset/scale/transform take base as first arg *)

(* Transparent proof (Defined) — should be extractable *)
Definition safe_pred (n : nat) (H : n > 0) : nat.
Proof.
  destruct n.
  - exfalso. inversion H.
  - exact n.
Defined.

(* Opaque proof (Qed) — should be erased or stubbed *)
Lemma add_comm_opaque : forall n m, n + m = m + n.
Proof.
  intros. lia.
Qed.

(* Use both transparent and section-abstracted defs *)
Definition test_offset : nat := offset 10 5.
Definition test_scale : nat := scale 3 4.
Definition test_transform : nat := transform 2 3.
Definition test_safe_pred : nat := safe_pred 5 (Nat.lt_0_succ 4).

(* Nested sections *)
Section Outer.
  Variable a : nat.
  Section Inner.
    Variable b : nat.
    Definition inner_add : nat := a + b.
    Definition inner_mul : nat := a * b.
  End Inner.
  Definition outer_use (b : nat) : nat := inner_add b + inner_mul b.
End Outer.

Definition test_inner : nat := inner_add 3 7.
Definition test_outer : nat := outer_use 4 5.

End ExtractDirectives.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.
Crane Extraction "extract_directives" ExtractDirectives.
