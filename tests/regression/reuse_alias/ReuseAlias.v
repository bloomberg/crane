From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Module ReuseAlias.

Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.

Arguments mynil {A}.
Arguments mycons {A}.

Fixpoint length {A : Type} (l : mylist A) : nat :=
  match l with
  | mynil => 0
  | mycons _ xs => S (length xs)
  end.

(** Increment the head — candidate for reuse optimization when use_count = 1. *)
Definition inc_head (l : mylist nat) : mylist nat :=
  match l with
  | mynil => mynil
  | mycons x xs => mycons (x + 1) xs
  end.

(** Use the same list twice: once through inc_head, once directly.
    If reuse fires on the first call (because evaluation order is
    unspecified), the second use of l sees the already-mutated list. *)
Definition double_use (l : mylist nat) : mylist nat * mylist nat :=
  (inc_head l, l).

(** Pass the same list to two different functions. *)
Definition double_call (l : mylist nat) : nat * nat :=
  (length l, length (inc_head l)).

(** Alias through let-binding, then use both the alias and the original
    in a match. *)
Definition alias_and_match (l : mylist nat) : mylist nat * nat :=
  let l2 := l in
  match l with
  | mynil => (l2, 0)
  | mycons x _ => (l2, x)
  end.

(** Build a result that refers to the scrutinee AND a pattern variable
    from the same match. *)
Definition scrutinee_in_branch (l : mylist nat) : mylist nat * mylist nat :=
  match l with
  | mynil => (mynil, mynil)
  | mycons _ xs => (l, xs)
  end.

(** Chain inc_head: each call might try to reuse. *)
Definition triple_inc (l : mylist nat) : mylist nat :=
  inc_head (inc_head (inc_head l)).

End ReuseAlias.

Crane Extraction "reuse_alias" ReuseAlias.
