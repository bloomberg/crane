(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Program Fixpoint with measure — Fix_F_sub/Acc wrapper terms. *)

From Stdlib Require Import Arith List Lia.
From Stdlib Require Import Program.Wf.
Import ListNotations.

Module ProgFix.

Program Fixpoint interleave (l1 l2 : list nat) {measure (length l1 + length l2)} : list nat :=
  match l1 with
  | [] => l2
  | x :: xs => x :: interleave l2 xs
  end.
Next Obligation. simpl. lia. Qed.

Definition test_interleave : list nat :=
  interleave [1; 3; 5] [2; 4; 6].

End ProgFix.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "program_fixpoint" ProgFix.
