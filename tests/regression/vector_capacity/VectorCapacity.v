(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Crane Require Import Monads.ITree.
From Crane Require Import External.Vector.

(** A fresh vector filled by a counted loop, one append per iteration, has
    its capacity reserved from the loop's count; any other filling shape is
    left to grow as it would. *)
Module VectorCapacity.

(** Reserved: exactly [n] appends. *)
Definition fill (n : nat) : itree vectorE (vector nat) :=
  v <- emptyVec nat ;;
  (fix f k := match k with
   | 0 => Ret v
   | S k' => push v k ;; f k'
   end) n.

(** Not reserved: the append is conditional. *)
Definition fill_even (n : nat) : itree vectorE (vector nat) :=
  v <- emptyVec nat ;;
  (fix f k := match k with
   | 0 => Ret v
   | S k' => (if Nat.even k then push v k else Ret tt) ;; f k'
   end) n.

(** Not reserved: two appends an iteration. *)
Definition fill_twice (n : nat) : itree vectorE (vector nat) :=
  v <- emptyVec nat ;;
  (fix f k := match k with
   | 0 => Ret v
   | S k' => push v k ;; push v k ;; f k'
   end) n.

(** Not reserved: the loop can stop early. *)
Definition fill_until_five (n : nat) : itree vectorE (vector nat) :=
  v <- emptyVec nat ;;
  (fix f k := match k with
   | 0 => Ret v
   | S k' => if Nat.eqb k 5 then Ret v else (push v k ;; f k')
   end) n.

End VectorCapacity.

Crane Extraction "vector_capacity" VectorCapacity.
