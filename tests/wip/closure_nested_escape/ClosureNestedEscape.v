From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ClosureNestedEscape.

(** A function takes a nat and returns a PAIR of fixpoints, both
    capturing the same parameter.

    BUG: Both fixpoints use [&] capture. They capture [n] by reference.
    Both are stored in a pair (constructor), so [return_captures_by_value]
    does NOT apply. After the function returns, [n] dangles.

    Difference from fix_escape_capture: returns TWO fixpoints that both
    capture the SAME variable. This tests whether both closures
    independently read garbage from the same dangling reference. *)

Definition make_pair_fix (n : nat) : (nat -> nat) * (nat -> nat) :=
  let fix add (x : nat) : nat :=
    match x with
    | O => n
    | S x' => S (add x')
    end
  in
  let fix mul (x : nat) : nat :=
    match x with
    | O => 0
    | S x' => n + mul x'
    end
  in (add, mul).

(** test1: make_pair_fix(5) returns (add, mul).
    add(3) = 5 + 3 = 8, mul(3) = 5 * 3 = 15.
    Expected: 8 + 15 = 23. *)
Definition test1 : nat :=
  let '(f, g) := make_pair_fix 5 in
  f 3 + g 3.

(** test2: With noise.
    add(0) = 7, mul(4) = 7 * 4 = 28.
    Expected: 7 + 28 = 35. *)
Definition test2 : nat :=
  let p := make_pair_fix 7 in
  let noise := 1 + 2 + 3 in
  fst p 0 + snd p 4.

(** test3: Only use one of the two fixpoints.
    mul(10) where n=3 → 3*10 = 30.
    Expected: 30. *)
Definition test3 : nat :=
  let '(_, g) := make_pair_fix 3 in
  g 10.

End ClosureNestedEscape.

Crane Extraction "closure_nested_escape" ClosureNestedEscape.
