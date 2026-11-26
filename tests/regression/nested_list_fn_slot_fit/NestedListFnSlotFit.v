(** Found by Ephyra round 28. A list of lists of two-argument functions,
    [list (list (bool -> nat -> nat))], given to [nth_or] whose result is
    [hd_or]'s list, the [hd_or] call partially applied as [map]'s function
    (so the element type is instantiated as [bool -> (nat -> nat)]). [nth_or]
    kept its type argument flat, [List<crane::fn<uint64_t(bool, uint64_t)>>],
    though its result went where [hd_or] takes the curried list: the
    expected type was compared with the type argument with namespace
    qualifiers in the way. The typed-fit check found the argument, built
    curried, in the flat slot (argument, convert); the C++ compiled through
    a [crane_convert] and was right.

    Fixed: a type argument takes its expected result's grouping whatever
    namespaces the two are written in ([Calls.regroup_by_expected],
    [Cpp_ir.Types.same_arrows_unqualified], [Cpp_ir.Types.regroup_as]). *)
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
