From Crane Require Import Mapping.NatInt.
From Crane Require Extraction.
From Stdlib Require Import List ZArith.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by
    hand.  The original was in a functor body; the functor is not needed.

    A local fixpoint's step matches on a match of a [Z] parameter, and one
    branch matches a list literal against [[_]], which Core writes as a let
    in a wildcard branch.  Lowering that branch's statements pushed the let's
    binder type and nothing popped it, so the sibling argument [rest] read
    the binder one further in: under CRANE_CHECK_IR=1 extraction failed the
    Core check "binder scopes: the variable at index 3 is x0_0 to the names
    in scope and _x to the binders typed in scope". *)
Module FunctorBinderScopeCheck.

Definition h (a : nat) (z : Z) (l : list nat) : nat -> nat :=
  let fix go (l : list nat) (acc : nat -> nat) {struct l} : nat -> nat :=
    match l with
    | [] => acc
    | _ :: rest =>
      go rest (match (match z with Z0 => false | _ => true end) with
               | true => match [0; 0] with [] => acc | [_] => acc | _ :: _ :: _ => (fun _ : nat => 1) end
               | false => (fun _ : nat => a) end)
    end in go l (fun _ : nat => 0).

Definition r_zero : nat := h 5 0%Z [1] 7.
Definition r_pos : nat := h 5 3%Z [1; 2] 7.
Definition r_empty : nat := h 5 3%Z [] 7.

End FunctorBinderScopeCheck.

Crane Extraction "functor_binder_scope_check" FunctorBinderScopeCheck.
