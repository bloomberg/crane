(** Found by Ephyra round 25. A polymorphic function instantiated at a
    function type, [pick] at [A := (nat -> nat) -> nat -> nat], fully applied
    and passed as the step of another polymorphic function ([twice]). Crane
    eta-expanded the call to the two arrows the instantiation adds past
    [pick]'s own and applied the [crane::fn] that [pick] returns to both at
    once, [pick<...>(true, f, g)(_x0, _x1)], while the type argument the call
    writes (the slot's grouping, [(nat -> nat) -> (nat -> nat)]) makes the
    result take one argument at a time ("no matching function for call to
    object of type 'crane::fn<...>'").

    Fixed: a call that fills its callee's declared parameters is written as
    the call whatever number of arrows the instantiation leaves after it
    ([Application.eta_fun]'s [saturated], which was limited to one); its
    result is the callable the type argument spells, evaluated once, as
    Rocq evaluates it. *)
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
