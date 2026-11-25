(** Found by Ephyra round 25. A local fixpoint applied to a literal list is
    unrolled in place; its non-empty branch calls a class-polymorphic
    function ([mconcat] over the [Mon (list A)] instance), and the result,
    appended to, is the argument of another local fixpoint whose result type
    differs ([list bool]). The generated C++ is right, but the typed-fit check
    finds the unrolled body's [list nat] value stored in a destination typed
    [list bool], the outer local fixpoint's result. With [mconcat] replaced by
    a literal, without the [++], or with the outer fixpoint at top level, the
    check passes.
    Expected: extracts under CRANE_CHECK_IR, [result = 4]. Actual: "Crane IR
    check (typed fit): a value of type list<nat> put in a slot of type
    list<bool> (destination, unrelated)". Seen under BDE and std mappings,
    also with primitive-array elements. *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Module LocalFixInlinedDictDestination.

Class Mon (A : Type) := { munit : A; mop : A -> A -> A }.
#[global] Instance mon_list {A : Type} : Mon (list A) := { munit := []; mop := @app A }.
Definition mconcat {A : Type} `{Mon A} (l : list A) : A := fold_right mop munit l.

Definition result : nat :=
  length (let fix go (l : list nat) {struct l} : list bool :=
            match l with [] => [] | x :: rest => Nat.even x :: go rest end in
          go ((let fix go2 (l2 : list nat) {struct l2} : list nat :=
                 match l2 with [] => [] | _ :: _ => mconcat [[1; 2]; [3]] end in go2 [4]) ++ [5])).

End LocalFixInlinedDictDestination.

Crane Extraction "local_fix_inlined_dict_destination" LocalFixInlinedDictDestination.
