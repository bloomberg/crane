From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List. Import ListNotations.
(** A rank-2 record field ([forall A, list A -> nat]) stores a methodified
    function as a value: the reference must become a method-calling lambda,
    not a hand-rolled forwarding call naming an undeducible type variable. *)

Module Rank2RecordField.
Record poly := P { sizer : forall A, list A -> nat }.
Definition pl : poly := P (fun A l => length l).
Definition go : nat := sizer pl nat [1;2] + sizer pl bool [true].
End Rank2RecordField.
Crane Extraction "rank2_record_field" Rank2RecordField.
