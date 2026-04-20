From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module FixViaSimpleLambda.

(** Two local fixpoints both capture a let-binding [base] via [&].
    They are combined in a simple lambda [fun x => ...] which captures
    them by [=] (since simple lambdas use value capture).

    BUG HYPOTHESIS: Copying a [std::function] that wraps a [&] lambda
    does NOT fix the dangling references. The [=] capture on the outer
    lambda copies the [std::function] objects, but the internal [&]
    closures still reference the destroyed stack variable [base].

    This is a different escape mechanism from existing tests:
    the fixpoints don't escape directly through a constructor —
    they escape INDIRECTLY by being captured in a simple lambda
    that is then stored in [Some]. *)

Definition make_combined (n : nat) : option (nat -> nat) :=
  let base := n * 2 in
  let fix double_add (x : nat) : nat :=
    match x with
    | O => base
    | S x' => 2 + double_add x'
    end
  in
  let fix triple_add (x : nat) : nat :=
    match x with
    | O => base
    | S x' => 3 + triple_add x'
    end
  in
  Some (fun x => double_add x + triple_add x).

(** test1: base=42, double_add(5) = 42+10 = 52,
    triple_add(5) = 42+15 = 57. Total = 109. *)
Definition test1 : nat :=
  match make_combined 21 with
  | Some f => f 5
  | None => 999
  end.

(** test2: With intervening computation to clobber the stack.
    base=200, double_add(0) = 200, triple_add(0) = 200. Total = 400. *)
Definition test2 : nat :=
  let opt := make_combined 100 in
  let noise := 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 in
  match opt with
  | Some f => f 0
  | None => noise
  end.

(** test3: Larger recursion depth to increase chance of stack corruption.
    base=10, double_add(20) = 10+40 = 50,
    triple_add(20) = 10+60 = 70. Total = 120. *)
Definition test3 : nat :=
  match make_combined 5 with
  | Some f => f 20
  | None => 999
  end.

End FixViaSimpleLambda.

Crane Extraction "fix_via_simple_lambda" FixViaSimpleLambda.
