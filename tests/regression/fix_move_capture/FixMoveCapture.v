From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module FixMoveCapture.

(** BUG HYPOTHESIS: dead-after analysis vs fixpoint [&] capture.

    Crane's move tracking computes [dead_in_a] for let-bindings:
    a variable is "dead" after a let's RHS if it does not appear
    free in the continuation. It then generates [std::move(var)].

    But [free_rels] only tracks DIRECT de Bruijn references.
    If a fixpoint captures a variable by [&] and the variable is
    later consumed by a let-binding (via a function that takes it
    by value), [free_rels] sees no direct reference in the
    continuation — so the variable is moved.

    The fixpoint's [&] reference then points to a moved-from
    shared_ptr (null). Calling the fixpoint dereferences null. *)

Inductive mylist : Type :=
  | mynil : mylist
  | mycons : nat -> mylist -> mylist.

Arguments mynil.
Arguments mycons _ _.

Fixpoint length (l : mylist) : nat :=
  match l with
  | mycons _ xs => 1 + length xs
  | mynil => 0
  end.

Fixpoint sum (l : mylist) : nat :=
  match l with
  | mycons h xs => h + sum xs
  | mynil => 0
  end.

(** [dup_head] stores [l] in the constructor → [l] escapes → owned.
    This means the caller passes [l] by value (move semantics). *)
Definition dup_head (l : mylist) : mylist :=
  match l with
  | mycons h xs => mycons h l
  | mynil => mynil
  end.

(** [f l]: defines a local fixpoint [go] that captures [l] by [&].
    Then [let t := dup_head l in ...]:
    - [dup_head] takes [l] by value (owned, because [l] escapes in its body)
    - Crane sees that [l] (dead_in_a) is not free in continuation [g 3 + length t]
    - Generates [dup_head(std::move(l))]
    - [l] is now null in caller scope
    - [g(3)] calls fixpoint, which accesses [l] via [&] → null → CRASH *)
Definition f (l : mylist) : nat :=
  let g := fix go (n : nat) : nat :=
    match n with
    | O => sum l
    | S m => 1 + go m
    end
  in
  let t := dup_head l in
  g 3 + length t.

Definition test1 : nat :=
  f (mycons 10 (mycons 20 (mycons 30 mynil))).
(** Expected: sum l = 60, g 3 = 63, length(dup_head l) = 4.
    Total = 63 + 4 = 67.
    BUG: g(3) crashes because l was moved into dup_head. *)

(** Even simpler: use the fixpoint, then pass [l] to a consuming
    function. The addition's evaluation order is unspecified in C++,
    so we use a let-binding to force the order. *)
Definition f2 (l : mylist) : nat :=
  let g := fix go (n : nat) : nat :=
    match n with
    | O => sum l
    | S m => 1 + go m
    end
  in
  let result_g := g 3 in
  let t := dup_head l in
  result_g + length t.

Definition test2 : nat :=
  f2 (mycons 5 (mycons 15 mynil)).
(** Expected: sum l = 20, g 3 = 23, length(dup_head l) = 3.
    Total = 23 + 3 = 26.
    BUG: Even with explicit ordering, if Crane moves [l] before
    [g(3)] is evaluated, the fixpoint crashes. *)

End FixMoveCapture.

Crane Extraction "fix_move_capture" FixMoveCapture.
