(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Set Crane FastVariant]: every inductive's alternatives in [crane::variant].
    Covers a value-type inductive and its matches, a loopified function (whose
    frames are a variant too), a coinductive (whose lazy cell holds one), and
    the driver's own matches through the [crane::] accessors. *)

From Stdlib Require Import List.
Import ListNotations.

Module FastVariant.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint insert (x : nat) (t : tree) : tree :=
  match t with
  | Leaf => Node Leaf x Leaf
  | Node l y r => if Nat.leb x y then Node (insert x l) y r else Node l y (insert x r)
  end.

Fixpoint sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l x r => sum l + x + sum r
  end.

Fixpoint size (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l _ r => S (size l + size r)
  end.

Definition build (l : list nat) : tree := fold_right insert Leaf l.

Inductive shape : Type :=
| Circle : nat -> shape
| Rect : nat -> nat -> shape
| Empty : shape.

Definition area (s : shape) : nat :=
  match s with
  | Circle r => 3 * r * r
  | Rect w h => w * h
  | Empty => 0
  end.

CoInductive stream : Type := Cons : nat -> stream -> stream.

CoFixpoint from (n : nat) : stream := Cons n (from (S n)).

Fixpoint take (n : nat) (s : stream) : list nat :=
  match n with
  | O => []
  | S k => match s with Cons x s' => x :: take k s' end
  end.

Definition sample : tree := build [5; 2; 8; 1; 9; 3].
Definition shapes : list shape := [Circle 2; Rect 3 4; Empty].
Definition first_three : list nat := take 3 (from 10).

End FastVariant.

Require Crane.Extraction.
From Crane Require Import Mapping.NatIntStd.
Set Crane FastVariant.
Set Crane Loopify.
Crane Extraction "fast_variant" FastVariant.
