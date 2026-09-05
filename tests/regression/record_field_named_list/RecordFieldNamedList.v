From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.

Module RecordFieldNamedList.

(** A record field named [list] shadows the [List] runtime type in the
    generated namespace, and constructor calls are emitted against the field
    name. *)
Record point := mkPoint { size : nat ; list : Datatypes.list nat ; count : nat }.

Definition weigh (p : point) : nat :=
  size p + List.length (list p) + count p.

Definition total : nat := weigh (mkPoint 1 [1;2;3] 5).

End RecordFieldNamedList.
Crane Extraction "record_field_named_list" RecordFieldNamedList.
