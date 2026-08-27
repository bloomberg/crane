From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List. Import ListNotations.
(** WIP: A record field with a rank-2 type (`forall A, list A -> nat`) emits a lambda
    body referring to an undeclared template parameter `_T1`. *)

Module Rank2RecordField.
Record poly := P { sizer : forall A, list A -> nat }.
Definition pl : poly := P (fun A l => length l).
Definition go : nat := sizer pl nat [1;2] + sizer pl bool [true].
End Rank2RecordField.
Crane Extraction "rank2_record_field" Rank2RecordField.
