(** An inductive whose name matches its enclosing module gets the module's C++
    namespace renamed out of the way, so the type and the namespace do not
    collide.  A record does not: its struct is emitted as the module struct
    itself, and a constant of that record's type then becomes an in-class
    static data member of the very type being defined, which is incomplete at
    that point. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.NatInt.

Module EponymousRecordOwnType.
  Record EponymousRecordOwnType : Set := Mk { field : nat }.

  Definition default_value : EponymousRecordOwnType := Mk 5.

  Definition answer : nat := field default_value.
End EponymousRecordOwnType.

Crane Extraction "eponymous_record_own_type" EponymousRecordOwnType.
