From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Memory safety: use after move.  A let-bound list [acc] is returned by a
    local fixpoint (captured by reference) and also captured by the
    [flat_map] closure.  The local fixpoint's return is lowered as
    [return std::move(acc);] because it looks like the last use, but the
    closure built afterwards copies the moved-from [acc]; [flat_map] then
    binds a reference through its null child (UBSan: reference binding to
    null pointer; a plain build segfaults).  Seen with and without
    [Set Crane Reuse]. *)
Module LocalFixMovesCapturedLocal.

Definition t : nat :=
  length (let acc := map (fun _ : nat => true) [0] in
          flat_map (fun _ : bool => acc)
            (let fix go (m : list nat) {struct m} : list bool :=
               match m with [] => acc | _ :: r => go r end in go [])).

End LocalFixMovesCapturedLocal.

Crane Extraction "local_fix_moves_captured_local" LocalFixMovesCapturedLocal.
