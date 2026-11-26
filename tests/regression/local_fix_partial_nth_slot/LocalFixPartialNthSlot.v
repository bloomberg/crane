(** Found by Ephyra round 28. [nth_or l 0], partially applied (so a function
    [nat -> nat] at [A := nat]), mapped over a list, where [l] is a local
    fixpoint call whose [nil] branch is a [flat_map]. The typed-fit check
    found the local fixpoint's [list nat] result put in a slot of type
    [list<fn(nat)->nat>] (destination, unrelated): the call's variables were
    read off its position's type, which states the closure over the missing
    argument, not the call's result, so the list argument was expected at
    [list (A -> A)]. The C++ compiled and was right.

    Fixed: a call given fewer arguments than it declares reads none of its
    variables off its position's type, as an over-applied call does not
    ([Calls.plan_call]'s [result_tvar_map]). *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Module LocalFixPartialNthSlot.

Definition nth_or {A : Type} (l : list A) (n : nat) (d : A) : A := nth n l d.
Definition result : nat :=
  fold_left Nat.add
    (map (nth_or (let fix go (l : list bool) {struct l} : list nat :=
                    match l with [] => flat_map (fun _ : bool => @nil nat) [] | _ :: r => [] end
                  in go []) 0) [1; 2]) 0.

End LocalFixPartialNthSlot.

Crane Extraction "local_fix_partial_nth_slot" LocalFixPartialNthSlot.
