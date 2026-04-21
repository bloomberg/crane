From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ClosureInCtor.

Inductive box :=
  | Box : (nat -> nat) -> box
  | Empty : box.

(** A local fixpoint captures the function parameter [n] and is stored
    in [Box] — a user-defined inductive (not option, not pair).

    BUG: Local fixpoints generate [std::function] with [&] capture
    (needed for self-reference). This [&] also captures [n] by reference.
    The fixpoint escapes through [Box], so [return_captures_by_value]
    does NOT apply. After [make_box_fix] returns, [n] is destroyed,
    and the captured reference dangles.

    Difference from fix_escape_capture: escapes through a CUSTOM
    INDUCTIVE constructor, not a pair. *)

Definition make_box_fix (n : nat) : box :=
  let fix add (x : nat) : nat :=
    match x with
    | O => n
    | S x' => S (add x')
    end
  in Box add.

(** test1: make_box_fix(5) returns Box(add) where add(x) = x + 5.
    Expected: add(3) = 5 + 3 = 8.
    Bug: [&] captures dangling reference to [n]. *)
Definition test1 : nat :=
  match make_box_fix 5 with
  | Box f => f 3
  | Empty => 999
  end.

(** test2: Interleave noise between closure creation and use.
    Expected: add(10) = 42 + 10 = 52. *)
Definition test2 : nat :=
  let b := make_box_fix 42 in
  let noise := 1 + 2 + 3 + 4 + 5 in
  match b with
  | Box f => f 10
  | Empty => 999
  end.

(** test3: Two boxes — capture different parameters.
    Expected: add_10(0) + add_20(0) = 10 + 20 = 30. *)
Definition test3 : nat :=
  let b1 := make_box_fix 10 in
  let b2 := make_box_fix 20 in
  match b1 with
  | Box f1 =>
    match b2 with
    | Box f2 => f1 0 + f2 0
    | Empty => 999
    end
  | Empty => 999
  end.

End ClosureInCtor.

Crane Extraction "closure_in_ctor" ClosureInCtor.
