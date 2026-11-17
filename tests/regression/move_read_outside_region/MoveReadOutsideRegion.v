(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a local was moved at a read that is not its last.  Translation
    decides a move from the continuation in front of the read, and a let's
    right-hand side, or a match standing in an argument, does not see what
    reads the variable after the let or beside the argument; nor does a read
    see the uses of a lifted polymorphic helper, which pass what it closes
    over at each call.  Each definition below moved [s] (or [n]) into [grow]
    (or the helper), which takes it by value, and then read the moved-from
    value: a segfault. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module MoveReadOutsideRegion.

Definition grow (l : list nat) : list nat := l ++ l.

(** A two-way case in an argument, read again beside it. *)
Definition if_in_argument (l : list nat) : nat :=
  let s := l ++ l in
  (if Nat.eqb (length (grow s)) 0 then 1 else 0) + length s.

(** A two-way case in a let's right-hand side, read again after the let. *)
Definition if_in_let (l : list nat) (b : bool) : nat :=
  let s := l ++ l in
  let x := (if b then (let z := grow s in length z + length z) else 0) in
  x + length s.

(** A match in a let's right-hand side, read again after the let. *)
Definition match_in_let (l : list nat) : nat :=
  let s := l ++ l in
  let x := (match l with nil => 0 | _ :: _ => let z := grow s in length z + length z end) in
  x + length s.

(** A two-way case beside a read in the same call. *)
Definition if_beside (l : list nat) (b : bool) : nat :=
  let s := l ++ l in
  length ((if b then grow s else nil) ++ s).

(** A match beside a read in the same call. *)
Definition match_beside (l : list nat) : nat :=
  let s := l ++ l in
  length ((match l with nil => nil | _ :: _ => grow s end) ++ s).

(** A polymorphic local helper closing over [n], used twice. *)
Definition helper_twice (n : nat) (b : bool) : nat :=
  let aux {A : Type} (a : A) : nat := List.length (List.repeat a n) in
  aux n + aux b.

Definition r_if_in_argument : nat := if_in_argument [1; 2].
Definition r_if_in_let : nat := if_in_let [1; 2] true.
Definition r_match_in_let : nat := match_in_let [1; 2].
Definition r_if_beside : nat := if_beside [1; 2] true.
Definition r_match_beside : nat := match_beside [1; 2].
Definition r_helper_twice : nat := helper_twice 2 true.

End MoveReadOutsideRegion.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "move_read_outside_region" MoveReadOutsideRegion.
