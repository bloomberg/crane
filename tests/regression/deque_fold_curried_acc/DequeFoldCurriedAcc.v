(** Found by Ephyra round 23. A variant of [deque_fold_function_acc]
    (round 20, fixed for a one-argument function accumulator): under
    [Mapping.DequeList], [fold_right] with a two-argument accumulator
    [nat -> bool -> nat].
    Expected: compiles, [result = 6].
    Fixed: "no viable overloaded '='" at [_a = _f( *_it, _a)]. The initial
    value was wrapped as [crane::fn([](uint64_t x) { return [=](bool b) ...;
    })], so class template argument deduction made the accumulator a
    [crane::fn] whose result is that inner closure's own type, while the
    step returns [crane::fn<crane::fn<uint64_t(bool)>(uint64_t)>]-shaped
    values. The wrap now names the type variable's instantiation, curried as
    a type variable spells it, and the call's result, which the mapping
    yields from that accumulator, is applied one argument at a time. *)
From Crane Require Import Mapping.NatInt Mapping.Std Mapping.DequeList.
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
