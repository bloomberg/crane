(** Found by Ephyra round 25. A local fixpoint applied to a literal list is
    unrolled in place; its non-empty branch calls a class-polymorphic
    function ([mconcat] over the [Mon (list A)] instance), and the result,
    appended to, is the argument of another local fixpoint whose result type
    differs ([list bool]). The generated C++ was right, but the typed-fit
    check found the unrolled body's [list nat] value stored in a destination
    typed [list bool]: the argument of the applied local fixpoint was
    generated with the enclosing result [list bool] as its return type, which
    [app]'s result bindings read as [A := bool].

    Fixed: an argument of an applied local fixpoint is generated with its
    parameter's type as the return type in force
    ([Local_functions.gen_applied_fix]). *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.
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
