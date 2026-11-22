(** Found by Ephyra round 23. A tail-recursive local fixpoint whose
    accumulator is a two-argument function [nat -> bool -> bool], applied
    to two more arguments, with the recursive call passing
    [fun _ : nat => acc 0] (a one-argument closure returning a partial
    application of [acc]). Akin to [fold_curried_fix_step] (round 22).
    Expected: compiles; [result = 1] ([r [1; 2] = true], [r [] = false]).
    Fixed: "no viable overloaded '='": the loop variable is the flat
    [crane::fn<bool(uint64_t, bool)>], and the update assigned it the curried
    closure [[=](uint64_t) { return [=](bool _pa0) {...}; }]. A lambda
    argument of a local function's call was written against the parameter's
    C++ type but not given its Core type as the slot, so the lambda did not
    take the binders the flat parameter takes; it now does, and is written
    [[=](uint64_t, bool eta0_) { return acc(0, eta0_); }]. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Import Extraction.
From Stdlib Require Import List.
Import ListNotations.

Module LoopAccCurriedPartialApp.

Definition r (l : list nat) : bool :=
  (let fix go (l : list nat) (acc : nat -> bool -> bool) {struct l} : nat -> bool -> bool :=
     match l with [] => acc | _ :: t => go t (fun _ : nat => acc 0) end
   in go l (fun n b => andb b (Nat.eqb n 0))) 5 true.

Definition result : nat := (if r [1; 2] then 1 else 0) + (if r [] then 10 else 0).

End LoopAccCurriedPartialApp.

Crane Extraction "loop_acc_curried_partial_app" LoopAccCurriedPartialApp.
