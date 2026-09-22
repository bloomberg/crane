From Crane Require Import Mapping.Std.
From CraneTestsRegression Require Import template_merge_outlined_member.A.
From CraneTestsRegression Require Import template_merge_outlined_member.Aux.

(** This file's name begins with the inductive's, which is what makes its
    top-level functions candidates to become methods of [box]'s struct.  The
    body names [Tally.bump], which lives in [Aux]'s struct -- emitted after
    every global-scope type, and unable to move in front of [box]. *)
Definition size {A : Set} (b : box A) : nat := Tally.bump (raw_size b).
