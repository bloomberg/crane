(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A top-level function with a function-typed parameter is emitted as a
    function template, deducing that parameter.  Passing its name as a value
    to a higher-order method then has no type to deduce. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import NatIntStd.
Require Import List.
Import ListNotations.

Module HofParamAsValue.
Definition ap (f : nat -> nat) (x : nat) : nat := f x.
Definition fs : list (nat -> nat) := [S; fun x => x * 2].
Definition run : nat := fold_right ap 1 fs.
End HofParamAsValue.

Crane Extraction "hof_param_as_value" HofParamAsValue.
