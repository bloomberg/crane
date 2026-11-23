(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Tests update_nth with bounds checking: both in-bounds and out-of-bounds cases.
   Exercises return-this via shared_from_this when the guard returns the list unchanged. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module UpdateNthBounds.

Definition update_nth {A} (n : nat) (x : A) (l : list A) : list A :=
  if n <? length l
  then firstn n l ++ x :: skipn (S n) l
  else l.

(* In-bounds update preserves length: update_nth 2 9 [1;2;3;4] has length 4 *)
Definition in_bounds_length : nat := length (update_nth 2 9 [1; 2; 3; 4]).

(* Out-of-bounds update preserves length: update_nth 9 7 [1;2;3] has length 3 *)
Definition out_of_bounds_length : nat := length (update_nth 9 7 [1; 2; 3]).

End UpdateNthBounds.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Crane Extraction "update_nth_bounds" UpdateNthBounds.
