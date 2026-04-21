From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Module FixComposeEscape.

(** A local fixpoint is composed with another function.

    The composition [fun x => g (add x)] creates a lambda with [=]
    capture, but the captured [add] is a [std::function] whose internal
    lambda uses [&] capture — it holds a reference to [base], a stack
    variable that is destroyed when [compose_add] returns.  The [=]
    capture copies the [std::function] VALUE, including its dangling
    [&] references. *)

Definition compose_add (base : nat) (g : nat -> nat) : nat -> nat :=
  let fix add (x : nat) : nat :=
    match x with
    | O => base
    | S x' => S (add x')
    end
  in fun x => g (add x).

(** test1: compose_add 42 id 3 = id (42 + 3) = 45 *)
Definition test1 : nat :=
  let f := compose_add 42 (fun x => x) in
  f 3.

(** test2: compose_add 10 double 5 = 2 * (10 + 5) = 30 *)
Definition test2 : nat :=
  let f := compose_add 10 (fun x => x * 2) in
  f 5.

(** test3: Compose two different compositions.
    compose_add 100 (compose_add 50 id)
    = fun x => (compose_add 50 id) (100 + x)
    = fun x => id (50 + (100 + x))
    = fun x => 150 + x
    test3 = 150 + 7 = 157 *)
Definition test3 : nat :=
  let inner := compose_add 50 (fun x => x) in
  let outer := compose_add 100 inner in
  outer 7.

End FixComposeEscape.

Crane Extraction "fix_compose_escape" FixComposeEscape.
