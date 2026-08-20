(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From Crane.Libraries.ParseALot.Utils Require Import DecEq.

(** Baseline realization of the [NativeMap] interface: a plain association
    list, keyed on any type with decidable equality (see [DecEq]). Unlike
    [Utils/NativeMap.v]'s [NativeMap], this is real, checked Coq code (no
    axioms, no extraction pragmas) — it extracts as an ordinary linear-scan
    list in both OCaml and C++ (Crane). It exists purely as a "no custom
    binding" comparison baseline, deliberately reusing the module name
    [NativeMap] so [Lexer/Memo/ConcreteMemo.v] doesn't need to change: to
    toggle, comment/uncomment which of [NativeMap.v] / [NativeMapBaseline.v]
    is [Require Import]ed there (only one may be imported at a time, since
    both define a module named [NativeMap]). *)

#[export] Instance Z_DecEq : Dec Z := Z.eq_dec.

Module NativeMap.

  (** A finite map from keys [K] to values [V], represented as an
      association list (most recent write first). *)
  Definition t (K V : Type) : Type := list (K * V).

  (** The empty map. *)
  Definition empty {K V} : t K V := [].

  (** Look up [k]; [None] if absent. Linear scan, most recent write wins. *)
  Fixpoint get {K V} `{Dec K} (m : t K V) (k : K) : option V :=
    match m with
    | [] => None
    | (k', v) :: m' => if dec_eq k k' then Some v else get m' k
    end.

  (** Insert [k |-> v] at the front; shadows any earlier binding for [k]. *)
  Definition set {K V} (m : t K V) (k : K) (v : V) : t K V := (k, v) :: m.

  Lemma get_empty : forall K V `{Dec K} (k : K), get (@empty K V) k = None.
  Proof. reflexivity. Qed.

  Lemma get_set : forall K V `{Dec K} (m : t K V) k v, get (set m k v) k = Some v.
  Proof.
    intros K V HD m k v. simpl. destruct (dec_eq k k) as [_ | Hne].
    - reflexivity.
    - contradiction Hne; reflexivity.
  Qed.

  Lemma get_set_moot : forall K V `{Dec K} (m : t K V) k k' v,
      k <> k' -> get (set m k v) k' = get m k'.
  Proof.
    intros K V HD m k k' v Hne. simpl. destruct (dec_eq k' k) as [Heq | _].
    - contradiction Hne. symmetry. exact Heq.
    - reflexivity.
  Qed.

End NativeMap.
