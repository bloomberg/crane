(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

(** A right fold of a map, fused into one traversal where both callbacks are
    pure under declared meanings and the mapped list is used once. *)
Module MapFoldFusion.

Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} a l.

Fixpoint map {A B : Type} (f : A -> B) (l : list A) : list B :=
  match l with
  | nil => nil
  | cons x xs => cons (f x) (map f xs)
  end.

Fixpoint foldr {A B : Type} (f : A -> B -> B) (z : B) (l : list A) : B :=
  match l with
  | nil => z
  | cons x xs => f x (foldr f z xs)
  end.

Fixpoint length {A : Type} (l : list A) : nat :=
  match l with
  | nil => 0
  | cons _ xs => S (length xs)
  end.

(** Fused: a declared operation, partly applied, and a declared operation. *)
Definition sum_succ (l : list nat) : nat := foldr Nat.add 0 (map (Nat.add 1) l).

(** Fused: lambdas, and a reducer that is not associative -- the fold's
    association is kept. *)
Definition alt_double (l : list nat) : nat :=
  foldr (fun x acc => x - acc) 0 (map (fun x => x * 2) l).

(** Fused across element types: the fold walks the map's input. *)
Definition count_big (l : list nat) : nat :=
  foldr (fun (b : bool) (acc : nat) => if b then S acc else acc) 0
    (map (fun x => Nat.ltb 2 x) l).

(** Declined: [twice] has no declared meaning. *)
Definition twice (x : nat) : nat := x + x.
Definition sum_twice (l : list nat) : nat := foldr Nat.add 0 (map twice l).

(** Declined: the mapped list is used twice. *)
Definition sum_and_length (l : list nat) : nat :=
  let m := map (Nat.mul 3) l in foldr Nat.add 0 m + length m.

End MapFoldFusion.

Crane Extraction "map_fold_fusion" MapFoldFusion.
