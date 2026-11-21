(** Found by Ephyra (round 20). [List.fold_left] with a function-typed
    accumulator under [Mapping.DequeList] (list as [std::deque]).

    Expected: compiles; [t_1 = 16] ([10 + 1 + 2 + 3]).

    Actual: compile error "no viable overloaded '='". The mapping spells the
    fold as [[](auto _f, const auto &_l, auto _a) { for (...) _a = _f(_a, _x);
    return _a; }(...)], so the accumulator's type is deduced from the initial
    value, a lambda closure type; each step returns a different closure,
    which cannot be assigned to it. The accumulator needs the fold's declared
    result type (a [crane::fn]). Also on main. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std Mapping.DequeList.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.
Module DequeFoldFunctionAcc.
Definition compose_all (l : list nat) : nat -> nat :=
  fold_left (fun (acc : nat -> nat) (k : nat) => fun x => acc x + k) l (fun x => x).
Definition t_1 : nat := compose_all [1; 2; 3] 10.
End DequeFoldFunctionAcc.
Crane Extraction "deque_fold_function_acc" DequeFoldFunctionAcc.
