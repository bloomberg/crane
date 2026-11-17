(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a value of a record or inductive instantiated at a sort, whose
    fields hold types -- [{| unwrap := nat |} : wrap Set], [{| pfst := nat;
    psnd := bool |} : pair Set Set] -- is built from thunks that throw.  A
    type in a value position is emitted as
    [([]() -> crane::obj { throw std::logic_error("unreachable"); })()]
    rather than as a placeholder, and the constants are initialised at
    program start, so the program aborts before [main] even though nothing
    reads them.  OCaml extraction writes [__] there. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module RecordAtSortTypeField.

Record wrap (A : Type) := { unwrap : A }.

Definition w : wrap Set := {| unwrap := nat |}.

Record pair (A B : Type) := { pfst : A; psnd : B }.

Definition tp : pair Set Set := {| pfst := nat; psnd := bool |}.

Inductive pr (A B : Type) := P : A -> B -> pr A B.

Definition p : pr Set nat := P _ _ bool 3.

Definition result : nat := match p with P _ _ _ n => n end.

End RecordAtSortTypeField.

Crane Extraction "record_at_sort_type_field" RecordAtSortTypeField.
