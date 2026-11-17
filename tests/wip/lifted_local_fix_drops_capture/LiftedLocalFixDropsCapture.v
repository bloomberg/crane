From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    A local fixpoint inside a polymorphic definition is lifted to a static
    template helper ([f_crane_go]), but the helper still reads the enclosing
    parameter [n], which it neither captures nor takes: "use of undeclared
    identifier 'n'". *)
Module LiftedLocalFixDropsCapture.

Definition f {A : Type} (x : A) (n : nat) : nat :=
  let fix go (l : list (bool * A)) (acc : nat) {struct l} : nat :=
    match l with [] => n | _ :: r => go r acc end in go [(false, x)] n.

Definition t : nat := f true 7.

End LiftedLocalFixDropsCapture.

Crane Extraction "lifted_local_fix_drops_capture" LiftedLocalFixDropsCapture.
