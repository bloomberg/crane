(** Found by Ephyra (round 22). A variant left by the round-20 fix of
    [deque_fold_function_acc]: [List.fold_left] with a function-typed
    accumulator under [Mapping.DequeList], whose initial value is the
    result of a local fixpoint rather than a lambda literal.

    Expected: compiles; [t_1 = 100 + 10 + 1 + 2 + 3 = 116].

    Actual: compile error "no viable overloaded '='". The fix wraps a lambda
    literal initial value in [crane::fn(...)], but here the initial value is
    an immediately invoked lambda that defines the fixpoint and returns a
    closure, so the mapping's [auto _a] is still a closure type that the
    step's closures do not assign to. Also on main. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std Mapping.DequeList.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.
Module DequeFoldFixInit.
Definition compose_all (l : list nat) (base : list nat) : nat -> nat :=
  fold_left (fun (acc : nat -> nat) (k : nat) => fun x => acc x + k) l
    (let fix go (m : list nat) (acc : nat -> nat) {struct m} : nat -> nat :=
       match m with [] => acc | j :: r => go r (fun x => acc x + j) end in
     go base (fun x => x)).
Definition t_1 : nat := compose_all [1; 2; 3] [10] 100.
End DequeFoldFixInit.
Crane Extraction "deque_fold_fix_init" DequeFoldFixInit.
