(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a record with a [Type] field that is used as data only inside
    an expression stays a C++ concept.  Such a record is demoted to a struct
    when it is used as a value, but demotion is triggered only by a
    declaration whose type mentions the record -- a constant
    [algs : list alg] (see [regression/record_with_type_field]).  Here the
    list [[natalg; natalg]] occurs only inside [result]'s body, so [alg] is
    still a concept: "use of concept 'alg' requires template arguments". *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module TypeFieldRecordInExpression.

Record alg := { ty : Type; unit_ : ty; f : ty -> nat }.

Definition natalg : alg := {| ty := nat; unit_ := 3; f := fun x => x |}.

Definition get (a : alg) : nat := f a (unit_ a).

Definition result : nat := List.length [natalg; natalg] + get natalg.

End TypeFieldRecordInExpression.

Crane Extraction "type_field_record_in_expression" TypeFieldRecordInExpression.
