From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
(** WIP: A record field whose type is a `Type`-valued `Fixpoint` applied to a literal
    (`ty 2`, i.e. a nested pair) is emitted as `uint64_t`, so the projections
    on it do not type-check. *)

Module TypeLevelFixpointRecordField.
Fixpoint ty (n : nat) : Type := match n with O => nat | S m => (ty m * ty m)%type end.
Record holder := H { lvl : nat ; val : ty 2 }.
Definition go : nat := fst (fst (val (H 2 ((1,2),(3,4))))).
End TypeLevelFixpointRecordField.
Crane Extraction "type_level_fixpoint_record_field" TypeLevelFixpointRecordField.
