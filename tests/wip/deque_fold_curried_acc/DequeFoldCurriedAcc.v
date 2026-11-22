(** Found by Ephyra round 23. A variant of [deque_fold_function_acc]
    (round 20, fixed for a one-argument function accumulator): under
    [Mapping.DequeList], [fold_right] with a two-argument accumulator
    [nat -> bool -> nat]. The initial value is wrapped as
    [crane::fn([](uint64_t x) { return [=](bool b) ... ; })], so class
    template argument deduction makes the accumulator a [crane::fn] whose
    result is that inner closure type, while the step takes and returns
    [crane::fn<crane::fn<uint64_t(bool)>(uint64_t)>]-shaped values.
    Expected: compiles, [result = 6].
    Actual: "no viable overloaded '='" at [_a = _f( *_it, _a)].
    Also on main. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std Mapping.DequeList.
From Crane Require Import Extraction.
From Stdlib Require Import List.
Import ListNotations.

Module DequeFoldCurriedAcc.

Definition g (l : list nat) : nat -> bool -> nat :=
  fold_right (fun (k : nat) (acc : nat -> bool -> nat) => fun x b => acc (x + k) b)
    (fun x b => if b then x else 0) l.

Definition result : nat := g [1; 2] 3 true.

End DequeFoldCurriedAcc.

Crane Extraction "deque_fold_curried_acc" DequeFoldCurriedAcc.
