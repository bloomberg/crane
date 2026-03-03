(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Bug 11: runtime move-capture reuse in repeated closure selector path. *)

From Stdlib Require Import Nat List.
Import ListNotations.

Module MoveCaptureReuse.

Definition prefix_each (prefix : list nat) (xss : list (list nat)) : list (list nat) :=
  List.map (fun xs => prefix ++ xs) xss.

Definition sample : list (list nat) :=
  prefix_each [1] [[10]; [20]].

Definition len_sum : nat :=
  match sample with
  | a :: b :: _ => List.length a + List.length b
  | _ => 0
  end.

End MoveCaptureReuse.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "move_capture_reuse" MoveCaptureReuse.