From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    A let (or a local fixpoint call) nested in the argument of another one
    fails the Core boundary check under CRANE_CHECK_IR=1 (the test suite's
    setting): "binder scopes: the variable at index 2 is a to the names in
    scope and q to the binders typed in scope".  Without the check the C++
    is right.

    - [f]: nested record updates through lets.
    - [g]: a local fixpoint call as the accumulator of another. *)
Module NestedBinderScopeCheck.

Record pt : Type := mkpt { px : nat; py : bool }.

Definition f (a : nat) : pt :=
  let p := (let q := mkpt 0 true in {| px := 0; py := py q |}) in
  {| px := a; py := py p |}.

Definition g (n : nat) : bool :=
  let fix go (l : list nat) (acc : bool) {struct l} : bool :=
    match l with [] => acc | _ :: _ => true end in
  go [] (let fix go2 (l : list nat) (acc : bool) {struct l} : bool :=
           match l with [] => true | _ :: _ => acc end in go2 [] true).

End NestedBinderScopeCheck.

Crane Extraction "nested_binder_scope_check" NestedBinderScopeCheck.
