(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The library [Lib.v] extracts with [Crane Recursive Extraction Library]:
    a file-level definition over [nat] and [list], so that the extraction
    also writes the standard library files it depends on. *)

From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Inductive t := T : nat -> t.

Definition get (x : t) : nat := match x with T n => n end.

Definition r : nat := get (T 4) + List.length [1; 2].
