From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ClosureLetEscape.

(** A local fixpoint captures a LET-BINDING (not a function parameter)
    and escapes through [Some] (std::optional).

    BUG: Local fixpoints use [&] capture. The let-binding [base] is a
    stack variable. The fixpoint escapes through [Some], so
    [return_captures_by_value] does NOT apply. After the function
    returns, [base] is destroyed, and the captured reference dangles.

    Difference from fix_escape_capture: captures a LET-BINDING
    (not a function parameter). The let-binding involves a computation
    ([n * 2]), so it can't be optimized away. *)

Definition make_fn_fix (n : nat) : option (nat -> nat) :=
  let base := n * 2 in
  let fix add (x : nat) : nat :=
    match x with
    | O => base
    | S x' => S (add x')
    end
  in Some add.

(** test1: make_fn_fix(21) => base=42, Some(add).
    add(3) = 42 + 3 = 45.
    Bug: [&] captures dangling reference to [base]. *)
Definition test1 : nat :=
  match make_fn_fix 21 with
  | Some f => f 3
  | None => 999
  end.

(** test2: With noise between closure creation and invocation.
    base = 100, noise = 15, add(noise) = 100 + 15 = 115. *)
Definition test2 : nat :=
  let opt := make_fn_fix 50 in
  let noise := 1 + 2 + 3 + 4 + 5 in
  match opt with
  | Some f => f noise
  | None => 999
  end.

(** test3: Captures from multiple let bindings.
    BUG: Both [a] and [b] are captured by [&], both dangle. *)
Definition make_fn_multi (n : nat) : option (nat -> nat) :=
  let a := n + 1 in
  let b := a * 3 in
  let fix helper (x : nat) : nat :=
    match x with
    | O => a + b
    | S x' => S (helper x')
    end
  in Some helper.

Definition test3 : nat :=
  match make_fn_multi 10 with
  | Some f => f 5
  | None => 999
  end.

End ClosureLetEscape.

Crane Extraction "closure_let_escape" ClosureLetEscape.
