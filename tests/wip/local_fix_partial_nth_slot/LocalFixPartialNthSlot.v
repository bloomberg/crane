(** Found by Ephyra round 28. [nth_or l 0], partially applied (so a function
    [nat -> nat] at [A := nat]), mapped over a list, where [l] is a local
    fixpoint call whose [nil] branch is a [flat_map]. The typed-fit check
    finds the local fixpoint's [list nat] result put in a slot of type
    [list<fn(nat)->nat>] (destination, unrelated): the list argument is
    planned at the partial application's type [A -> A] instead of [A]. The
    same with the fixpoint's branch a literal [[]], or with the [flat_map]
    passed directly, passes. The C++ compiles and is right. Expected:
    extracts under CRANE_CHECK_IR, [result = 3]. Actual: "Crane IR check
    (typed fit): a value of type ns (list)<(nat)> put in a slot of type ns
    (list)<fn((nat))->(nat)> (destination, unrelated)". *)
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
