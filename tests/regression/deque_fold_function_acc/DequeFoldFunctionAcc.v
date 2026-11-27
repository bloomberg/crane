(** Found by Ephyra (round 20). [List.fold_left] with a function-typed
    accumulator under [Mapping.DequeList] (list as [std::deque]).

    Expected: compiles; [t_1 = 16] ([10 + 1 + 2 + 3]).

    Fixed: compile error "no viable overloaded '='". The mapping spells the
    fold as [[](auto _f, const auto &_l, auto _a) { for (...) _a = _f(_a, _x);
    return _a; }(...)], so the accumulator's type was deduced from the
    initial value, a lambda closure type (or, for a global, a function
    pointer); each step returns a different closure, which cannot be
    assigned to it. An argument of a mapped operation at a parameter declared
    at a type variable, instantiated at a function type, now arrives as the
    [crane::fn] its closures convert to. [t_2] covers [fold_right], a global
    initial value, and the mapped [map] building functions ([t_2 = 20]). *)
From Crane Require Import Mapping.NatInt Mapping.Std Mapping.DequeList.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.
Module DequeFoldFunctionAcc.
Definition compose_all (l : list nat) : nat -> nat :=
  fold_left (fun (acc : nat -> nat) (k : nat) => fun x => acc x + k) l (fun x => x).
Definition t_1 : nat := compose_all [1; 2; 3] 10.
(** The same through [fold_right], and with a global function as the
    initial value. *)
Definition compose_right (l : list nat) : nat -> nat :=
  fold_right (fun (k : nat) (acc : nat -> nat) => fun x => acc x * k) (fun x => x) l.
Definition twice (x : nat) : nat := x + x.
Definition compose_glob (l : list nat) : nat -> nat :=
  fold_left (fun (acc : nat -> nat) (k : nat) => fun x => acc x + k) l twice.
(** A list of functions built by the mapped [map], applied. *)
Definition adders (l : list nat) : list (nat -> nat) := map (fun k x => x + k) l.
Definition t_2 : nat := compose_right [2; 3] 1 + compose_glob [1] 5
  + fold_left (fun a f => f a) (adders [1; 2]) 0.
End DequeFoldFunctionAcc.
Crane Extraction "deque_fold_function_acc" DequeFoldFunctionAcc.
