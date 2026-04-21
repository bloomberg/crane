From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module FixDirectReturn.

(** A local fixpoint is captured by an outer lambda and returned.
    Crane can't uncurry here because the fixpoint is used as a VALUE
    inside the returned lambda (not fully applied at the return site).

    BUG: The inner fixpoint [add] uses [&] capture. Even though the
    outer lambda uses [=] capture (via return_captures_by_value),
    the COPY of [add] (a std::function) inside the outer lambda
    still holds [&] references to the destroyed stack variables. *)

Definition make_callback (base : nat) : (nat -> nat) -> nat :=
  let fix add (x : nat) : nat :=
    match x with
    | O => base
    | S x' => S (add x')
    end
  in fun g => g (add 0) + add 1.

(** test1: make_callback(42)(fun x => x) = id(42) + 43 = 85. *)
Definition test1 : nat :=
  let cb := make_callback 42 in
  cb (fun x => x).

(** test2: make_callback(10)(fun x => x * 2) = 20 + 11 = 31. *)
Definition test2 : nat :=
  let cb := make_callback 10 in
  cb (fun x => x * 2).

(** test3: Nested — use the closure from make_callback inside another
    make_callback. *)
Definition test3 : nat :=
  let cb1 := make_callback 5 in
  let cb2 := make_callback 100 in
  cb1 (fun _ => cb2 (fun x => x)).

End FixDirectReturn.

Crane Extraction "fix_direct_return" FixDirectReturn.
