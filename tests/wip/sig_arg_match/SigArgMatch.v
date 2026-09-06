(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [proj1_sig] applied to a [sig] argument.  The generated accessor compares
    the whole [Sig] value against a numeric precondition and destructures it
    with a structured binding, neither of which compiles. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import List.
Import ListNotations.

Module SigArgMatch.
Definition pos := { n : nat | 0 < n }.
Definition one : pos := exist _ 1 (le_n 1).
Definition addp (p q : pos) : nat := proj1_sig p + proj1_sig q.
Definition ps : list pos := [one; one].
Definition run : nat := fold_right (fun p acc => proj1_sig p + acc) 0 ps + addp one one.
End SigArgMatch.

Crane Extraction "sig_arg_match" SigArgMatch.run.
