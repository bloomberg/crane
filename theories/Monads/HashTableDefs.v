(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The flavour-free half of the mutable hash tables of [STHashTable] and
    [GlobalHashTable], after Haskell's [hashtables] package: the
    [Hashable] class of keys and the pure operations on one bucket.

    A table is separate chaining: an array of buckets, each an association
    list holding at most one entry per key.  A key's bucket is its [hash]
    modulo the number of buckets. *)

From Stdlib Require Import
  Arith.PeanoNat
  Bool
  List
.

Import ListNotations.

(** Keys: a hash, and an equality that equal keys hash alike under. *)
Class Hashable (A : Type) : Type := {
  hash : A -> nat;
  eqb : A -> A -> bool
}.

(** A natural number is its own hash. *)
#[global] Instance hashable_nat : Hashable nat :=
  {| hash (n : nat) := n; eqb := Nat.eqb |}.

(** [false] hashes to [0], [true] to [1]. *)
#[global] Instance hashable_bool : Hashable bool :=
  {| hash (b : bool) := if b then 1 else 0; eqb := Bool.eqb |}.

(** A pair mixes its components' hashes; in C++ the arithmetic wraps. *)
#[global] Instance hashable_prod {A B : Type} `{Hashable A} `{Hashable B}
  : Hashable (A * B) :=
  {| hash (p : A * B) := hash (fst p) * 31 + hash (snd p);
     eqb (p q : A * B) := eqb (fst p) (fst q) && eqb (snd p) (snd q) |}.

(** A list's hash mixes its elements', first element last. *)
Fixpoint list_hash {A : Type} `{Hashable A} (xs : list A) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => hash x + 31 * list_hash xs'
  end.

(** Two lists are equal when they have equal elements pairwise. *)
Fixpoint list_eqb {A : Type} `{Hashable A} (xs ys : list A) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => eqb x y && list_eqb xs' ys'
  | _, _ => false
  end.

(** Lists of hashable elements are hashable. *)
#[global] Instance hashable_list {A : Type} `{Hashable A} : Hashable (list A) :=
  {| hash := list_hash; eqb := list_eqb |}.

(** One bucket: the entries whose keys share a bucket, at most one per key. *)
Definition bucket (K A : Type) : Type := list (K * A).

Section Buckets.

  Context {K A : Type} `{Hashable K}.

  (** The bucket of [k] among [n] buckets; [n] is never [0]. *)
  Definition index (k : K) (n : nat) : nat := Nat.modulo (hash k) n.

  (** The value bound to [k] in [b], if any. *)
  Fixpoint bucket_find (k : K) (b : bucket K A) : option A :=
    match b with
    | [] => None
    | (k', v) :: rest => if eqb k k' then Some v else bucket_find k rest
    end.

  (** [b] without the entry for [k]. *)
  Fixpoint bucket_remove (k : K) (b : bucket K A) : bucket K A :=
    match b with
    | [] => []
    | (k', v) :: rest => if eqb k k' then rest else (k', v) :: bucket_remove k rest
    end.

  (** [b] with [k] bound to what [o] says: [Some v] binds it to [v], [None]
      unbinds it. *)
  Definition bucket_put (k : K) (o : option A) (b : bucket K A) : bucket K A :=
    match o with
    | Some v => (k, v) :: bucket_remove k b
    | None => bucket_remove k b
    end.

End Buckets.

(** Whether [o] holds a value. *)
Definition present {A : Type} (o : option A) : bool :=
  match o with
  | Some _ => true
  | None => false
  end.

(** The number of buckets of a table that [new] makes. *)
Definition default_capacity : nat := 8.
