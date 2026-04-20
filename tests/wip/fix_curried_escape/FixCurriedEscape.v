From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Module FixCurriedEscape.

(** A local fixpoint that escapes through an option wrapper,
    preventing Crane from uncurrying it away.

    [make_fn] defines a local fixpoint [go] with [&] capture of
    [base] (a stack variable).  Wrapping in [Some] forces
    the fixpoint to be stored as a [std::function], because the
    return type [option (nat -> nat)] cannot be uncurried.

    BUG: The [std::function] holds [&] references to [base].
    After [make_fn] returns, [base] is destroyed, and calling
    the extracted function accesses freed memory. *)

Definition make_fn (base : nat) : option (nat -> nat) :=
  let fix go (x : nat) : nat :=
    match x with
    | O => base
    | S x' => S (go x')
    end
  in Some go.

(** test1: unwrap and call — go captures base=42.
    go 3 = 42 + 3 = 45. *)
Definition test1 : nat :=
  match make_fn 42 with
  | Some f => f 3
  | None => 999
  end.

(** test2: Different base to clobber the stack.
    make_fn 10 -> go captures base=10.
    go 7 = 10 + 7 = 17. *)
Definition test2 : nat :=
  match make_fn 10 with
  | Some f => f 7
  | None => 999
  end.

(** test3: Call make_fn twice — stack reuse should clobber [base].
    First call returns go1 with base=100.
    Second call reuses the stack frame with base=0.
    If go1 reads the clobbered base, it returns 0+5=5 instead of 100+5=105. *)
Definition test3 : nat :=
  let fn1 := make_fn 100 in
  let _ := make_fn 0 in
  match fn1 with
  | Some f => f 5
  | None => 999
  end.

End FixCurriedEscape.

Crane Extraction "fix_curried_escape" FixCurriedEscape.
