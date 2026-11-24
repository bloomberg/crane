(** Found by Ephyra round 24, fixed. A [match] on a case expression one of
    whose branches binds a [let]: the scrutinee is lowered to an immediately
    invoked lambda ([auto &&_sv = [&]() -> t3 { ... }();]), and the
    typed-fit check under [CRANE_CHECK_IR] put the values that lambda
    returns in the slot of the enclosing function's result.  The C++ was
    right; extraction failed.  The lambda's returns now go to its own result
    ([Match.iife_return]).

    - [on_t3]: a two-constructor inductive; was "a value of type t3 put in a
      slot of type nat".
    - [on_z]: [Z] without a mapping, the shape the generator found (under
      BDE and std alike).

    Expected: extracts under [CRANE_CHECK_IR]; [on_t3 true 4 = 0],
    [on_t3 false 4 = 1], [on_z true 4 = 0], [on_z false 4 = 1]. *)
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Extraction.
From Stdlib Require Import ZArith.

Module TypedFitScrutineeLet.

Inductive t3 : Type := A | B (n : nat).

Definition on_t3 (b : bool) (n : nat) : nat :=
  match (if b then A else let k := Nat.add n 1 in B k) with A => 0 | B _ => 1 end.

Definition on_z (b : bool) (n : nat) : nat :=
  match (if b then 0%Z else let k := Nat.add n 1 in Z.of_nat k) with Z0 => 0 | _ => 1 end.

End TypedFitScrutineeLet.

Crane Extraction "typed_fit_scrutinee_let" TypedFitScrutineeLet.
