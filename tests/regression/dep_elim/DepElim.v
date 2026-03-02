(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Dependent elimination and indexed types. *)

From Stdlib Require Import Nat Bool List.
Import ListNotations.

Module DepElim.

(* === Fin: bounded natural numbers === *)

Inductive fin : nat -> Type :=
  | FZ : forall n, fin (S n)
  | FS : forall n, fin n -> fin (S n).

Fixpoint fin_to_nat {n : nat} (f : fin n) : nat :=
  match f with
  | FZ _ => 0
  | FS _ f' => S (fin_to_nat f')
  end.

(* === Vector: length-indexed list === *)

Inductive vec (A : Type) : nat -> Type :=
  | vnil : vec A 0
  | vcons : forall n, A -> vec A n -> vec A (S n).

Arguments vnil {A}.
Arguments vcons {A n} _ _.

Fixpoint vec_to_list {A : Type} {n : nat} (v : vec A n) : list A :=
  match v with
  | vnil => []
  | vcons x xs => x :: vec_to_list xs
  end.

Fixpoint vec_map {A B : Type} {n : nat} (f : A -> B) (v : vec A n) : vec B n :=
  match v with
  | vnil => vnil
  | vcons x xs => vcons (f x) (vec_map f xs)
  end.

Definition vec_head {A : Type} {n : nat} (v : vec A (S n)) : A :=
  match v with
  | vcons x _ => x
  end.

Definition vec_tail {A : Type} {n : nat} (v : vec A (S n)) : vec A n :=
  match v with
  | vcons _ xs => xs
  end.

(* === Option indexed by availability === *)

Inductive avail : bool -> Type :=
  | present : nat -> avail true
  | absent : avail false.

Definition get_present (a : avail true) : nat :=
  match a with
  | present n => n
  end.

(* === Test values === *)

Definition test_fin0 : nat := fin_to_nat (FZ 2).
Definition test_fin2 : nat := fin_to_nat (FS 2 (FS 1 (FZ 0))).

Definition my_vec : vec nat 3 := vcons 10 (vcons 20 (vcons 30 vnil)).
Definition test_vec_list : list nat := vec_to_list my_vec.
Definition test_vec_head : nat := vec_head my_vec.
Definition test_vec_tail_list : list nat := vec_to_list (vec_tail my_vec).
Definition test_vec_map : list nat := vec_to_list (vec_map (fun n => n + 1) my_vec).

Definition test_present : nat := get_present (present 42).

End DepElim.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "dep_elim" DepElim.
