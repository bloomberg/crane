(** Found by Ephyra (round 22). A variant left by the round-20 fix of
    [deque_fold_function_acc]: [List.fold_left] with a function-typed
    accumulator under [Mapping.DequeList], whose initial value is the
    result of a local fixpoint ([t_1]) or a let-bound lambda ([t_2]) rather
    than a lambda literal.

    Expected: compiles; [t_1 = 100 + 10 + 1 + 2 + 3 = 116] and [t_2 = 1].

    Fixed: compile error "no viable overloaded '='". The round-20 fix
    wrapped the initial value in [crane::fn(...)] only where it was written
    as a lambda or a function's name; here it is an immediately invoked
    lambda that defines the fixpoint (or binds [c]) and returns a closure,
    so the mapping's [auto _a] was still a closure type that the step's
    closures do not assign to.  An argument of a mapping at a parameter
    declared at a type variable instantiated at a function type is now
    wrapped whatever it is written as. *)
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

(** The same with a let-bound lambda as the initial value. *)
Definition with_let (b : bool) : list nat -> list nat :=
  fold_left (fun (acc : list nat -> list nat) (_ : nat) => acc) [0]
    (let c := negb b in fun l => if c then 1 :: l else l).

Definition t_2 : nat := List.length (with_let false []).
End DequeFoldFixInit.
Crane Extraction "deque_fold_fix_init" DequeFoldFixInit.
