(** Found by Ephyra round 25. A polymorphic function instantiated at a
    function type, [twice] at [A := nat -> nat], whose step is a [let] of a
    two-argument local function followed by a lambda that partially applies
    it, [let cf := fun y j => ... in fun c => cf (c 1)]. The generated C++ is
    right, but the typed-fit check finds the partial application, a closure
    [nat -> nat], stored in a destination typed [nat]: the lambda's result is
    typed as if the step had the flat arity of [A -> A]. Naming the step as a
    top-level function, or dropping [twice], passes the check.
    Expected: extracts under CRANE_CHECK_IR, [result = 20]. Actual: "Crane IR
    check (typed fit): a value of type closure (nat)->nat put in a slot of type
    nat (destination, unrelated) in ... h". *)
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
