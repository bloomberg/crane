From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module FixCaptureFnArg.

(** A local fixpoint captures a FUNCTION argument AND is returned
    through a pair (preventing uncurrying).

    BUG: [go] uses [&] capture. Both [f] (a std::function on the
    caller's stack) and [base] are captured by reference.
    The fixpoint escapes through the pair — after [make_transform]
    returns, [f] (the std::function object), [base], and the local
    [go] are all destroyed. The returned closure dereferences a
    destroyed std::function when it calls [f]. *)

Definition make_transform (f : nat -> nat) (base : nat)
  : nat * (nat -> nat) :=
  let fix go (x : nat) : nat :=
    match x with
    | O => f base
    | S x' => S (go x')
    end
  in (f base, go).

(** test1: make_transform(x=>x*2, 5) = (10, go).
    go(3) = (5*2) + 3 = 13. Total = 10 + 13 = 23. *)
Definition test1 : nat :=
  let '(n, g) := make_transform (fun x => x * 2) 5 in
  n + g 3.

(** test2: make_transform(S, 10) = (11, go).
    go(5) = S(10) + 5 = 16. Total = 11 + 16 = 27. *)
Definition test2 : nat :=
  let '(n, g) := make_transform S 10 in
  n + g 5.

End FixCaptureFnArg.

Crane Extraction "fix_capture_fn_arg" FixCaptureFnArg.
