From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Set Crane Loopify.

(** A lent parameter of a value inductive is passed by const reference
    whether its type names the inductive or an abbreviation of it
    ([Translation_support.names_value_inductive]); a frame machine holds one
    so by pointer. *)
Module LentAliasByReference.

Definition bag := list nat.

Definition table (A : Type) := list (nat * A).

(** An abbreviation of an abbreviation. *)
Definition big_bag := bag.

(** Read only: lent, by const reference. *)
Definition bag_size (b : bag) : nat := length b.

Definition big_bag_size (b : big_bag) : nat := length b.

(** Not tail recursive: a frame machine, whose frames point at the cells of
    the lent bag rather than copying them. *)
Fixpoint bag_sum (b : bag) : nat :=
  match b with
  | nil => 0
  | x :: r => x + bag_sum r
  end.

Fixpoint lookup {A : Type} (k : nat) (d : A) (t : table A) : A :=
  match t with
  | nil => d
  | (k', v) :: r => if Nat.eqb k k' then v else lookup k d r
  end.

(** Two lent abbreviation-typed parameters, walked in step. *)
Fixpoint dot (a : bag) (b : bag) : nat :=
  match a, b with
  | x :: a', y :: b' => x * y + dot a' b'
  | _, _ => 0
  end.

(** Kept whole: owned, by value, moved in. *)
Definition push (x : nat) (b : bag) : bag := x :: b.

Definition sample : bag := 1 :: 2 :: 3 :: 4 :: nil.

Definition names : table nat := (1, 10) :: (2, 20) :: (3, 30) :: nil.

Definition test_size : nat := bag_size sample.
Definition test_big_size : nat := big_bag_size (push 0 sample).
Definition test_sum : nat := bag_sum sample.
Definition test_lookup_hit : nat := lookup 2 0 names.
Definition test_lookup_miss : nat := lookup 7 99 names.
Definition test_dot : nat := dot sample (push 5 sample).

End LentAliasByReference.

Crane Extraction "lent_alias_by_reference" LentAliasByReference.
