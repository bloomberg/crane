(** Found by Ephyra round 25. A polymorphic function instantiated at a
    function type, [pick] at [A := (nat -> nat) -> nat -> nat], fully applied
    and passed as the step of another polymorphic function ([twice]). Crane
    eta-expands the argument to two binders and applies the [crane::fn] that
    [pick] returns to both at once, [pick<...>(true, f, g)(_x0, _x1)], but the
    returned [crane::fn] takes one argument and returns another [crane::fn].
    Expected: compiles, [result = 30]. Actual: "no matching function for call
    to object of type 'crane::fn<crane::fn<unsigned long long (unsigned long
    long)> (crane::fn<unsigned long long (unsigned long long)>)>'". *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.

Module PickCurriedFnOverapply.

Definition pick {A : Type} (b : bool) (x y : A) : A := if b then x else y.

Definition twice {A : Type} (f : A -> A) (x : A) : A := f (f x).

Definition result : nat :=
  twice (pick true (fun (g : nat -> nat) (n : nat) => g (S n)) (fun g n => g n))
    (fun n => n * 10) 1.

End PickCurriedFnOverapply.

Crane Extraction "pick_curried_fn_overapply" PickCurriedFnOverapply.
