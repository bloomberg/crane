(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Set Crane SharedVariant] on inductives that hold themselves other than
    as a direct field: a rose tree's children in a list, an optional child,
    and mutual inductives holding each other; and on a large one that does
    not hold itself at all. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module SharedVariantNested.

Inductive rose := RNode : nat -> list rose -> rose.

Fixpoint rsum (t : rose) : nat :=
  match t with
  | RNode n ts => n + fold_left (fun acc t => acc + rsum t) ts 0
  end.

Fixpoint rbump (t : rose) : rose :=
  match t with RNode n ts => RNode (S n) (map rbump ts) end.

Definition r0 : rose := RNode 1 [RNode 2 []; RNode 3 [RNode 4 []]].
Definition r1 : rose := rbump r0.

Inductive chain := Link : nat -> option chain -> chain.

Fixpoint clen (c : chain) : nat :=
  match c with
  | Link _ None => 1
  | Link _ (Some c') => S (clen c')
  end.

Definition c0 : chain := Link 1 (Some (Link 2 (Some (Link 3 None)))).

Inductive stmt :=
  | Assign : nat -> expr -> stmt
  | Seq : stmt -> stmt -> stmt
  | Skip : stmt
with expr :=
  | Num : nat -> expr
  | Add : expr -> expr -> expr
  | Block : stmt -> expr -> expr.

Fixpoint ssize (s : stmt) : nat :=
  match s with
  | Assign _ e => 1 + esize e
  | Seq a b => ssize a + ssize b
  | Skip => 1
  end
with esize (e : expr) : nat :=
  match e with
  | Num _ => 1
  | Add a b => esize a + esize b
  | Block s e => ssize s + esize e
  end.

Definition s0 : stmt := Seq (Assign 1 (Add (Num 2) (Block Skip (Num 3)))) Skip.

(** Not recursive, but large: a value is one word all the same. *)
Inductive shape := Point | Box3 : nat -> nat -> nat -> shape.

Definition volume (s : shape) : nat :=
  match s with Point => 0 | Box3 a b c => a * b * c end.

Definition shapes : list shape := [Box3 2 3 4; Point; Box3 1 1 1].

Definition result : nat :=
  rsum r0 + rsum r1 + clen c0 + ssize s0 + fold_left (fun n s => n + volume s) shapes 0.

End SharedVariantNested.

Set Crane SharedVariant.
Crane Extraction "shared_variant_nested" SharedVariantNested.
