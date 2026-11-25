(** Found by Ephyra round 25. A polymorphic function instantiated at a
    function type, [twice] at [A := nat -> nat], whose step is a [let] of a
    two-argument local function followed by a lambda that partially applies
    it, [let cf := fun y j => ... in fun c => cf (c 1)]. The generated C++ was
    right, but the typed-fit check found the partial application, a closure
    [nat -> nat], stored in a destination typed [nat]: an argument written
    as a [let] got no slot type, so the lambda it ends in was typed at the
    flat arity of [A -> A].

    Fixed: a [let] in argument position is the value its body is, and is
    written against the parameter as that body would be
    ([Calls.argument_position]). *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.

Module TwiceComposedFnDestination.

Definition twice {A : Type} (f : A -> A) (x : A) : A := f (f x).

Definition h (k : nat) : nat -> nat :=
  twice (let cf := fun (y : nat) (j : nat) => y + j + k in
         fun c : nat -> nat => cf (c 1)) (fun j => j * 10).

Definition result : nat := h 2 5.

End TwiceComposedFnDestination.

Crane Extraction "twice_composed_fn_destination" TwiceComposedFnDestination.
