From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module FixHigherOrder.

(** A wrapper function that takes a function and stores it in [Some]. *)
Definition wrap_fn (f : nat -> nat) : option (nat -> nat) := Some f.

(** Creates a fixpoint and passes it through [wrap_fn].
    The fixpoint escapes through the function call, not through
    direct constructor application.

    BUG HYPOTHESIS: When the fixpoint is passed as an argument to
    [wrap_fn], the translation may use [&] capture. [wrap_fn] stores
    it in [Some] and returns. After [make_wrapped] returns, the
    captured [base] is destroyed. *)

Definition make_wrapped (base : nat) : option (nat -> nat) :=
  let fix go (x : nat) : nat :=
    match x with
    | O => base
    | S x' => S (go x')
    end
  in wrap_fn go.

(** test1: make_wrapped(5) -> Some(go), go(3) = 5+3 = 8. *)
Definition test1 : nat :=
  match make_wrapped 5 with
  | Some f => f 3
  | None => 999
  end.

(** test2: with noise between creation and use. *)
Definition test2 : nat :=
  let o := make_wrapped 42 in
  let noise := 1 + 2 + 3 + 4 + 5 in
  match o with
  | Some f => f 10 + noise
  | None => 999
  end.

(** Two layers of wrapping: fixpoint passed through two functions. *)
Definition double_wrap (f : nat -> nat) : option (option (nat -> nat)) :=
  Some (Some f).

Definition make_double_wrapped (base : nat) : option (option (nat -> nat)) :=
  let fix go (x : nat) : nat :=
    match x with
    | O => base
    | S x' => S (go x')
    end
  in double_wrap go.

(** test3: Doubly wrapped fixpoint. go(7) = 100+7 = 107. *)
Definition test3 : nat :=
  match make_double_wrapped 100 with
  | Some (Some f) => f 7
  | _ => 999
  end.

End FixHigherOrder.

Crane Extraction "fix_higher_order" FixHigherOrder.
