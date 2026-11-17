(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** An instance declared in a wrapper module ([Sizes]) lifts a helper out of
    its method.  The helper used to travel through a queue the next element
    emptied, so it was called and never declared; it now comes back from the
    instance's generation and is emitted ahead of the instance struct. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
From CraneTestsRegression Require Import wrapper_instance_lifted_helper.Sizes.
Import ListNotations.

Module WrapperInstanceLiftedHelper.

Definition use : nat := @size _ sized_pair ([1; 2], [true]) + twice 1.

End WrapperInstanceLiftedHelper.

Crane Extraction "wrapper_instance_lifted_helper" WrapperInstanceLiftedHelper.
