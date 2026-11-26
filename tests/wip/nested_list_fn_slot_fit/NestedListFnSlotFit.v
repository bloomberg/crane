(** Found by Ephyra round 28. A list of lists of two-argument functions,
    [list (list (bool -> nat -> nat))], given to [nth_or] whose result is
    [hd_or]'s list, the [hd_or] call partially applied as [map]'s function (so
    the element type is instantiated as [bool -> (nat -> nat)]). The typed-fit
    check finds the argument, whose inner element type is curried,
    [list<list<fn(bool)->fn(nat)->nat>>], put in a slot spelled flat,
    [list<list<fn(bool,nat)->nat>>] (argument, convert); the C++ compiles and
    is right. With one level of list ([hd_or d []] directly) the check
    passes. Variant of [nested_curried_instantiation]. Expected: extracts
    under CRANE_CHECK_IR, [result = 13]. Actual: "Crane IR check (typed fit):
    ... (argument, convert)". *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Module NestedListFnSlotFit.

Definition hd_or {A : Type} (d : A) (l : list A) : A := match l with [] => d | x :: _ => x end.
Definition nth_or {A : Type} (l : list A) (n : nat) (d : A) : A := nth n l d.
Definition result : nat :=
  fold_left (fun a f => a + f 6)
    (map (hd_or (fun (b : bool) (n : nat) => if b then n else 1)
                (nth_or (@nil (list (bool -> nat -> nat))) 0 (@nil (bool -> nat -> nat))))
       [true; false; true]) 0.

End NestedListFnSlotFit.

Crane Extraction "nested_list_fn_slot_fit" NestedListFnSlotFit.
