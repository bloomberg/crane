From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.
Set Crane Loopify.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Under Loopify, a non-tail recursive function that re-matches its own
    argument inside the recursive branch ([match n with O => [] | S _ => h m
    end ++ h m]) builds a continuation frame from [_x], a name only declared as
    a member of that frame: "use of undeclared identifier '_x'".  The
    continuation after the inner match runs in its [S _x] branch, where
    [_x] has the level of the let binding the match's value, [_tmp2]; the
    frame picked the innermost local of that level.  The recursion plan now
    names a live binder with its site, and the frame keeps the local bound
    there. *)
Module LoopifyRematchFrameBinder.

Fixpoint h (n : nat) : list bool :=
  match n with O => [] | S m => (match n with O => [] | S _ => h m end) ++ h m end.

End LoopifyRematchFrameBinder.

Crane Extraction "loopify_rematch_frame_binder" LoopifyRematchFrameBinder.
