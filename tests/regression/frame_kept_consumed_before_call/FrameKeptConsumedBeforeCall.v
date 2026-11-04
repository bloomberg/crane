(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A frame machine keeping a variable that a call made before the frame
    is saved consumes.

    Under Crane Reuse the list [pairs] walks is owned, so a field of its
    cell is the region's own.  The frame saving [x] across the recursive
    call reads it after [snoc x] does, and the plan did not count that
    read: [snoc] took [x] by move, and the frame kept the moved-from list.
    [again] passes [x] to the recursive call too, which, evaluated after
    the frame is saved, may take it. *)

From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module FrameKeptConsumedBeforeCall.

Fixpoint snoc (x : list nat) : list nat :=
  match x with
  | [] => [0]
  | h :: t => h :: snoc t
  end.

Fixpoint pairs (fuel : nat) (l : list (list nat)) : list (list nat) :=
  match fuel with
  | O => l
  | S k =>
    match l with
    | [] => []
    | [x] => [x]
    | x :: z :: rest =>
      let y := snoc x in
      let r := pairs k (z :: rest) in
      x :: y :: r
    end
  end.

Fixpoint again (fuel : nat) (l : list (list nat)) : list (list nat) :=
  match fuel with
  | O => l
  | S k =>
    match l with
    | [] => []
    | [x] => [x]
    | x :: z :: rest =>
      let y := snoc x in
      let r := again k (x :: rest) in
      y :: x :: r
    end
  end.

End FrameKeptConsumedBeforeCall.

Set Crane Loopify.
Set Crane NonAtomicRc.
Set Crane Reuse.
Crane Extraction "frame_kept_consumed_before_call" FrameKeptConsumedBeforeCall.
