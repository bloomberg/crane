(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: [Set Crane Extraction File Comment] writes the comment into the
    generated C++ with OCaml's delimiters, [(*Copyright Example Corp *)], at
    file scope: "expected ')'".  Any use of the option breaks every header
    it writes. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module FileCommentDelimiters.

Definition result : nat := 3.

End FileCommentDelimiters.

Set Crane Extraction File Comment "Copyright Example Corp".
Crane Extraction "file_comment_delimiters" FileCommentDelimiters.
