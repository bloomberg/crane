From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** [sumk] is tail recursive and is loopified into a [for], so it should run in
    constant stack.  It does not: the continuation parameter [k] is a
    [std::function] taken by value and then *copied* into the next
    continuation's capture, rather than moved out of the dying parameter.  Each
    iteration therefore copies the whole chain, and copying a chain of a
    hundred thousand nested [std::function]s recurses a hundred thousand deep
    and overflows the stack. *)

Module CpsContinuationCopy.

  Fixpoint sumk (l : list nat) (k : nat -> nat) : nat :=
    match l with
    | [] => k 0
    | x :: r => sumk r (fun s => k (x + s))
    end.

  Definition run : nat := sumk (List.seq 0 100000) (fun x => x).

End CpsContinuationCopy.

Crane Extraction "cps_continuation_copy" CpsContinuationCopy.
