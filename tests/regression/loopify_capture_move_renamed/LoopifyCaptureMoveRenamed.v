From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

Set Crane Loopify.

(** A continuation captured by move, in a function loopified.

    [partition_cps] hands the recursive call a new continuation that closes
    over the old one, [k], for the last time: the closure takes [k] by move.
    Loopified, [k] becomes the loop variable [_loop_k], and the closure is
    written over it at every turn.  The closure's reads were renamed but its
    capture move was not, so it went on moving from [k], which the loop had
    already moved into [_loop_k] on entry: a read of a moved-from value, and
    the continuation it did read copied. *)

Module LoopifyCaptureMoveRenamed.

Fixpoint partition_cps (p : nat -> bool) (l : list nat)
  (k : list nat -> list nat -> nat) : nat :=
  match l with
  | [] => k [] []
  | x :: rest =>
    partition_cps p rest (fun yes no =>
      if p x then k (x :: yes) no
      else k yes (x :: no))
  end.

Definition count_evens (l : list nat) : nat :=
  partition_cps Nat.even l (fun yes _ => length yes).

Definition count_odds (l : list nat) : nat :=
  partition_cps Nat.even l (fun _ no => length no).

End LoopifyCaptureMoveRenamed.

Crane Extraction "loopify_capture_move_renamed" LoopifyCaptureMoveRenamed.
