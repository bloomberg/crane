(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: in a record with a [Type] field that is used as data, a field
    holding a lambda that uses its argument concretely -- [toN := fun b =>
    if b then 1 else 0] -- is emitted as a generic lambda, and the
    [crane_erase_fn] adapter instantiates it at [crane::obj]: "value of type
    'const crane::obj' is not contextually convertible to 'bool'".  A
    lambda binder is spelled at its concrete type only where the body
    decomposes it (a structured binding or a member access); a condition,
    arithmetic or a call is a concrete use just the same.  It shows once the
    record is demoted to a struct, here by [algs : list alg]. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module TypeFieldRecordConcreteLambda.

Record alg := { T : Type; z : T; toN : T -> nat }.

Definition bool_alg : alg := {| T := bool; z := true; toN := fun b => if b then 1 else 0 |}.
Definition nat_alg : alg := {| T := nat; z := 2; toN := fun n => n |}.

Definition run (a : alg) : nat := toN a (z a).

Definition algs : list alg := [nat_alg; bool_alg].

Definition result : nat := fold_left (fun acc a => acc + run a) algs 0.

End TypeFieldRecordConcreteLambda.

Crane Extraction "type_field_record_concrete_lambda" TypeFieldRecordConcreteLambda.
