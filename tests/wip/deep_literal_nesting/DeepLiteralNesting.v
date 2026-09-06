(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Literals that extract to deeply nested constructor applications: a
    computed list, and a unary [nat].  Both are emitted as one expression per
    element, and clang exhausts its parser stack on the result. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import List.
Import ListNotations.

Module DeepLiteralNesting.

Definition big : list nat := Eval compute in seq 0 400.
Definition n : nat := 3000.
Definition run : nat := length big + n.

End DeepLiteralNesting.

Crane Extraction "deep_literal_nesting" DeepLiteralNesting.run.
