From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module FixEscapeCapture.

(** A local fixpoint that captures a function parameter and is returned
    in a pair. The fixpoint's [&] capture creates a dangling reference
    to the captured parameter after the enclosing function returns. *)
Definition make_pair_fn (base : nat) : nat * (nat -> nat) :=
  let fix add (x : nat) : nat :=
    match x with
    | O => base
    | S x' => S (add x')
    end
  in (base, add).

(** Invokes the escaped fixpoint — use-after-free if [&] capture. *)
Definition test_pair : nat :=
  let '(_, f) := make_pair_fn 5 in
  f 3.

(** Same pattern with a non-recursive local fixpoint to isolate the
    capture issue from self-reference. *)
Definition make_pair_fn2 (base : nat) : nat * (nat -> nat) :=
  let fix id_add (x : nat) : nat :=
    match x with
    | O => base
    | S x' => S (id_add x')
    end
  in (id_add base, id_add).

Definition test_pair2 : nat :=
  let '(n, f) := make_pair_fn2 5 in
  n + f 3.

End FixEscapeCapture.

Crane Extraction "fix_escape_capture" FixEscapeCapture.
