(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*
   Test coinductive types and corecursive definitions.
   These might trigger different code paths in extraction.
*)
Require Import Crane.Mapping.NatInt.
Require Crane.Extraction.

Module Coinductive.

(* Infinite stream coinductive type *)
CoInductive stream : Type :=
| Cons : nat -> stream -> stream.

(* Corecursive definition - infinite stream of zeros *)
CoFixpoint zeros : stream := Cons 0 zeros.

(* Corecursive definition - infinite stream counting from n *)
CoFixpoint count_from (n : nat) : stream := Cons n (count_from (S n)).

(* Head of stream *)
Definition hd (s : stream) : nat :=
  match s with
  | Cons x _ => x
  end.

(* Tail of stream *)
Definition tl (s : stream) : stream :=
  match s with
  | Cons _ xs => xs
  end.

(* Map over stream (corecursive) *)
CoFixpoint smap (f : nat -> nat) (s : stream) : stream :=
  match s with
  | Cons x xs => Cons (f x) (smap f xs)
  end.

(* Interleave two streams *)
CoFixpoint interleave (s1 s2 : stream) : stream :=
  match s1 with
  | Cons x xs => Cons x (interleave s2 xs)
  end.

(* Extract corecursive values differently *)
Definition get_zeros : stream := zeros.
Definition get_count : stream := count_from 0.

Definition test_hd := hd get_zeros.
Definition test_count := get_count.

(* Nested coinductive *)
CoInductive tree : Type :=
| Leaf : nat -> tree
| Node : nat -> tree -> tree -> tree.

CoFixpoint infinite_tree (n : nat) : tree :=
  Node n (infinite_tree (n + 1)) (infinite_tree (n + 2)).

End Coinductive.

Crane Extraction "coinductive" Coinductive.
