From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Module FramePushMovesScrutineeField.
  (** The inner fixpoint's machine matches [s], which it owns, binding its
      head [x] by reference into it.  The frame saved for [weigh1 ys] keeps
      [x], which what follows reads; the call passes [s] on whole.  Moving
      [x] into the frame leaves the [s] the call is given without its head. *)
  Fixpoint weigh (s : list (list nat)) : list nat -> nat :=
    fix weigh1 (t : list nat) : nat :=
      match s, t with
      | x :: xs, _ :: ys => weigh1 ys + length x + weigh xs t
      | _, _ => 0
      end.

  (** 5 + 12 + ... : [weigh [x2] t] is [2 * length t], so
      [weigh1 t] is [weigh1 ys + 3 + 2 * length t]: 5, 12, 21. *)
  Definition result : nat := weigh [[1; 2; 3]; [4; 5]] [7; 8; 9].
End FramePushMovesScrutineeField.

Set Crane Loopify.
Crane Extraction "frame_push_moves_scrutinee_field" FramePushMovesScrutineeField.
