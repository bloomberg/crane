From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.

Module NameClashScopeLeak.

(** Test scope isolation between if-else branches.
    With std::visit, each branch was a lambda with its own scope.
    With if/else-if, we rely on { } blocks for scoping. *)

(** Match on list, return list. Both branches produce the same type. *)
Definition rotate (l : list nat) : list nat :=
  match l with
  | nil => nil
  | x :: rest => rest ++ (x :: nil)
  end.

(** Two consecutive matches on different lists in the same function. *)
Definition heads_sum (l1 l2 : list nat) : nat :=
  let h1 := match l1 with nil => 0 | x :: _ => x end in
  let h2 := match l2 with nil => 0 | x :: _ => x end in
  h1 + h2.

(** Match on list, and in the Cons branch, match on the tail. *)
Definition first_two_sum (l : list nat) : nat :=
  match l with
  | nil => 0
  | x :: rest =>
    match rest with
    | nil => x
    | y :: _ => x + y
    end
  end.

(** Match where both branches contain let bindings with same name. *)
Definition branch_let_clash (l : list nat) : nat :=
  match l with
  | nil =>
    let result := 0 in result
  | x :: _ =>
    let result := x * 2 in result
  end.

(** Three consecutive matches, each with same binding variable name pattern. *)
Definition triple_head (l1 l2 l3 : list nat) : nat :=
  let a := match l1 with nil => 0 | x :: _ => x end in
  let b := match l2 with nil => 0 | x :: _ => x end in
  let c := match l3 with nil => 0 | x :: _ => x end in
  a + b + c.

(** Matching on a pair where both components are lists. *)
Definition pair_match (p : list nat * list nat) : nat :=
  let (l1, l2) := p in
  let h1 := match l1 with nil => 0 | x :: _ => x end in
  let h2 := match l2 with nil => 0 | x :: _ => x end in
  h1 + h2.

End NameClashScopeLeak.

Crane Extraction "name_clash_scope_leak" NameClashScopeLeak.
