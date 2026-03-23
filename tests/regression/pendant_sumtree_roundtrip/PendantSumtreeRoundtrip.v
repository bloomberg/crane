(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: dependent pendant roundtrip, heterogenous ledger values, and sumtree validation. *)

From Stdlib Require Import List Bool Arith Lia Vectors.Vector Vectors.Fin.
Import ListNotations.
Import VectorNotations.

Module PendantSumtreeRoundtripCase.

Definition digit : Type := Fin.t 10.

Definition digit_to_nat (d : digit) : nat :=
  proj1_sig (Fin.to_nat d).

Definition digit_of_nat (n : nat) (H : n < 10) : digit :=
  Fin.of_nat_lt H.

Lemma lt_0_10 : 0 < 10. Proof. lia. Qed.
Lemma lt_1_10 : 1 < 10. Proof. lia. Qed.
Lemma lt_2_10 : 2 < 10. Proof. lia. Qed.
Lemma lt_3_10 : 3 < 10. Proof. lia. Qed.
Lemma lt_4_10 : 4 < 10. Proof. lia. Qed.
Lemma lt_5_10 : 5 < 10. Proof. lia. Qed.
Lemma lt_6_10 : 6 < 10. Proof. lia. Qed.
Lemma lt_7_10 : 7 < 10. Proof. lia. Qed.
Lemma lt_9_10 : 9 < 10. Proof. lia. Qed.

Definition digit0 : digit := digit_of_nat 0 lt_0_10.
Definition digit1 : digit := digit_of_nat 1 lt_1_10.
Definition digit2 : digit := digit_of_nat 2 lt_2_10.
Definition digit3 : digit := digit_of_nat 3 lt_3_10.
Definition digit4 : digit := digit_of_nat 4 lt_4_10.
Definition digit5 : digit := digit_of_nat 5 lt_5_10.
Definition digit6 : digit := digit_of_nat 6 lt_6_10.
Definition digit7 : digit := digit_of_nat 7 lt_7_10.
Definition digit9 : digit := digit_of_nat 9 lt_9_10.

Fixpoint value_digits {n : nat} (ds : Vector.t digit n) : nat :=
  match ds with
  | [] => 0
  | d :: tl => digit_to_nat d + 10 * value_digits tl
  end.

Fixpoint list_to_vector_opt (n : nat) (xs : list digit) : option (Vector.t digit n) :=
  match n with
  | 0 =>
      match xs with
      | List.nil => Some []
      | _ => None
      end
  | S n' =>
      match xs with
      | List.nil => None
      | List.cons x tl =>
          match list_to_vector_opt n' tl with
          | Some v => Some (x :: v)
          | None => None
          end
      end
  end.

Lemma list_to_vector_opt_to_list :
  forall n (ds : Vector.t digit n),
    list_to_vector_opt n (Vector.to_list ds) = Some ds.
Proof.
  intros n ds.
  induction ds as [|d n tl IH].
  - reflexivity.
  - rewrite to_list_cons. simpl. rewrite IH. reflexivity.
Qed.

Definition encode_multi {n : nat} (nums : list (Vector.t digit n))
  : list (list digit) :=
  List.map Vector.to_list nums.

Definition decode_multi {n : nat} (segments : list (list digit))
  : option (list (Vector.t digit n)) :=
  let decoded := List.map (list_to_vector_opt n) segments in
  List.fold_right
    (fun ov acc =>
      match ov, acc with
      | Some v, Some vs => Some (List.cons v vs)
      | _, _ => None
      end)
    (Some List.nil)
    decoded.

Theorem decode_multi_encode_multi_roundtrip :
  forall n (nums : list (Vector.t digit n)),
    decode_multi (encode_multi nums) = Some nums.
Proof.
  intros n nums.
  induction nums as [|ds tl IH].
  - reflexivity.
  - unfold decode_multi, encode_multi in *. simpl.
    rewrite list_to_vector_opt_to_list. rewrite IH. reflexivity.
Qed.

Inductive Twist : Type := TS | TZ.
Inductive Fiber : Type := Cotton | Camelid.
Inductive Color : Type := White | Brown | Red | Blue.

Record CordMeta : Type := {
  cm_fiber : Fiber;
  cm_color : Color;
  cm_spin  : Twist;
  cm_ply   : Twist
}.

Record CertifiedPendant (n : nat) : Type := {
  cp_meta : CordMeta;
  cp_digits : Vector.t digit n;
  cp_roundtrip :
    decode_multi (encode_multi (List.cons cp_digits List.nil)) =
    Some (List.cons cp_digits List.nil)
}.

Arguments cp_meta {n} _.
Arguments cp_digits {n} _.

Definition pendant_digits {n : nat} (p : CertifiedPendant n) : option (Vector.t digit n) :=
  match decode_multi (encode_multi (List.cons (cp_digits p) List.nil)) with
  | Some (List.cons ds List.nil) => Some ds
  | _ => None
  end.

Definition pendant_value {n : nat} (p : CertifiedPendant n) : option nat :=
  option_map value_digits (pendant_digits p).

Definition Ledger : Type := list { n : nat & CertifiedPendant n }.

Fixpoint ledger_values (l : Ledger) : list (option nat) :=
  match l with
  | List.nil => List.nil
  | List.cons (existT _ _ p) tl => List.cons (pendant_value p) (ledger_values tl)
  end.

Record PendantGroup (n : nat) : Type := {
  pg_top : CertifiedPendant n;
  pg_pendants : list (CertifiedPendant n)
}.

Arguments pg_top {n} _.
Arguments pg_pendants {n} _.

Definition group_sums_validb {n : nat} (g : PendantGroup n) : bool :=
  match pendant_value (pg_top g) with
  | None => false
  | Some top_val =>
      let pendant_vals := List.map (@pendant_value n) (pg_pendants g) in
      let sum_opt := List.fold_right
        (fun ov acc =>
          match ov, acc with
          | Some v, Some a => Some (v + a)
          | _, _ => None
          end)
        (Some 0)
        pendant_vals in
      match sum_opt with
      | Some s => Nat.eqb top_val s
      | None => false
      end
  end.

Inductive SumTree (n : nat) : Type :=
| SumLeaf : CertifiedPendant n -> SumTree n
| SumNode : CertifiedPendant n -> list (SumTree n) -> SumTree n.

Arguments SumLeaf {n} _.
Arguments SumNode {n} _ _.

Fixpoint sumtree_top {n : nat} (st : SumTree n) : CertifiedPendant n :=
  match st with
  | SumLeaf p => p
  | SumNode p _ => p
  end.

Fixpoint sumtree_leaves {n : nat} (st : SumTree n) : list (CertifiedPendant n) :=
  match st with
  | SumLeaf p => [p]
  | SumNode _ children => List.concat (List.map sumtree_leaves children)
  end.

Fixpoint sumtree_depth {n : nat} (st : SumTree n) : nat :=
  match st with
  | SumLeaf _ => 1
  | SumNode _ children =>
      S (List.fold_right Nat.max 0 (List.map sumtree_depth children))
  end.

Fixpoint sumtree_validb_aux {n : nat} (fuel : nat) (st : SumTree n) : bool :=
  match fuel with
  | 0 => true
  | S fuel' =>
      match st with
      | SumLeaf _ => true
      | SumNode top children =>
          let child_tops := List.map sumtree_top children in
          let g := {| pg_top := top; pg_pendants := child_tops |} in
          group_sums_validb g && List.forallb (sumtree_validb_aux fuel') children
      end
  end.

Definition sumtree_validb {n : nat} (st : SumTree n) : bool :=
  sumtree_validb_aux (sumtree_depth st) st.

Definition sumtree_leaf_total {n : nat} (st : SumTree n) : option nat :=
  let vals := List.map (@pendant_value n) (sumtree_leaves st) in
  List.fold_right
    (fun ov acc =>
      match ov, acc with
      | Some v, Some a => Some (v + a)
      | _, _ => None
      end)
    (Some 0)
    vals.

Fixpoint nat_list_eqb (xs ys : list nat) : bool :=
  match xs, ys with
  | List.nil, List.nil => true
  | List.cons x xs', List.cons y ys' => Nat.eqb x y && nat_list_eqb xs' ys'
  | _, _ => false
  end.

Definition option_nat_eqb (x y : option nat) : bool :=
  match x, y with
  | Some a, Some b => Nat.eqb a b
  | None, None => true
  | _, _ => false
  end.

Definition option_nat_is_some (x : option nat) : bool :=
  match x with
  | Some _ => true
  | None => false
  end.

Definition digit_vec1 (a : digit) : Vector.t digit 1 := [a].
Definition digit_vec3 (a b c : digit) : Vector.t digit 3 := [a; b; c].

Definition sample_meta_a : CordMeta := {|
  cm_fiber := Cotton;
  cm_color := Brown;
  cm_spin := TS;
  cm_ply := TZ
|}.

Definition sample_meta_b : CordMeta := {|
  cm_fiber := Camelid;
  cm_color := Red;
  cm_spin := TZ;
  cm_ply := TS
|}.

Definition sample_meta_c : CordMeta := {|
  cm_fiber := Cotton;
  cm_color := Blue;
  cm_spin := TS;
  cm_ply := TS
|}.

Definition digits_731 : Vector.t digit 3 := digit_vec3 digit1 digit3 digit7.
Definition digits_462 : Vector.t digit 3 := digit_vec3 digit2 digit6 digit4.
Definition digits_269 : Vector.t digit 3 := digit_vec3 digit9 digit6 digit2.
Definition digits_200 : Vector.t digit 3 := digit_vec3 digit0 digit0 digit2.
Definition digits_069 : Vector.t digit 3 := digit_vec3 digit9 digit6 digit0.
Definition digits_5 : Vector.t digit 1 := digit_vec1 digit5.

Definition pendant_731 : CertifiedPendant 3 := {|
  cp_meta := sample_meta_a;
  cp_digits := digits_731;
  cp_roundtrip := @decode_multi_encode_multi_roundtrip 3 (List.cons digits_731 List.nil)
|}.

Definition pendant_462 : CertifiedPendant 3 := {|
  cp_meta := sample_meta_b;
  cp_digits := digits_462;
  cp_roundtrip := @decode_multi_encode_multi_roundtrip 3 (List.cons digits_462 List.nil)
|}.

Definition pendant_269 : CertifiedPendant 3 := {|
  cp_meta := sample_meta_c;
  cp_digits := digits_269;
  cp_roundtrip := @decode_multi_encode_multi_roundtrip 3 (List.cons digits_269 List.nil)
|}.

Definition pendant_200 : CertifiedPendant 3 := {|
  cp_meta := sample_meta_b;
  cp_digits := digits_200;
  cp_roundtrip := @decode_multi_encode_multi_roundtrip 3 (List.cons digits_200 List.nil)
|}.

Definition pendant_069 : CertifiedPendant 3 := {|
  cp_meta := sample_meta_c;
  cp_digits := digits_069;
  cp_roundtrip := @decode_multi_encode_multi_roundtrip 3 (List.cons digits_069 List.nil)
|}.

Definition pendant_5 : CertifiedPendant 1 := {|
  cp_meta := sample_meta_a;
  cp_digits := digits_5;
  cp_roundtrip := @decode_multi_encode_multi_roundtrip 1 (List.cons digits_5 List.nil)
|}.

Definition sample_multi_digits : list (Vector.t digit 3) :=
  [digits_731; digits_462; digits_269].

Definition sample_multi_roundtrip_ok : bool :=
  match decode_multi (encode_multi sample_multi_digits) with
  | Some decoded =>
      nat_list_eqb (List.map (@value_digits 3) decoded) [731; 462; 269]
  | None => false
  end.

Definition sample_group : PendantGroup 3 := {|
  pg_top := pendant_731;
  pg_pendants := [pendant_462; pendant_269]
|}.

Definition sample_subtree : SumTree 3 :=
  SumNode pendant_269 [SumLeaf pendant_200; SumLeaf pendant_069].

Definition sample_tree : SumTree 3 :=
  SumNode pendant_731 [SumLeaf pendant_462; sample_subtree].

Definition sample_ledger : Ledger :=
  List.cons (existT _ 3 pendant_731)
    (List.cons (existT _ 3 pendant_462)
      (List.cons (existT _ 1 pendant_5) List.nil)).

Definition sample_group_valid : bool :=
  group_sums_validb sample_group.

Definition sample_subtree_valid : bool :=
  sumtree_validb sample_subtree.

Definition sample_tree_valid : bool :=
  sumtree_validb sample_tree.

Definition sample_leaf_total_matches_root : bool :=
  option_nat_eqb (sumtree_leaf_total sample_tree) (pendant_value pendant_731).

Definition sample_tree_depth : nat :=
  sumtree_depth sample_tree.

Definition sample_ledger_entry_count : nat :=
  List.length (ledger_values sample_ledger).

Definition sample_ledger_all_present : bool :=
  List.forallb option_nat_is_some (ledger_values sample_ledger).

End PendantSumtreeRoundtripCase.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "pendant_sumtree_roundtrip" PendantSumtreeRoundtripCase.
