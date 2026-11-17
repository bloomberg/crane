(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A record's field whose type is an alias of a function type, applied.
    The field is a data member of the alias's type -- [pred<Nat>] is
    [crane::fn<bool(Nat)>] -- so it is called with as many arguments as
    that function takes.  The call read the field's arity off the alias,
    which is no arrow, called it with none and applied the result:
    [h.run()(n)]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module RecordFieldFunctionAlias.
  Definition pred (A : Type) : Type := A -> bool.
  Definition rel (A : Type) : Type := A -> A -> bool.

  Record holder := { run : pred nat; same : rel nat }.

  Definition apply_run (h : holder) (n : nat) : bool := run h n.
  Definition apply_same (h : holder) (a b : nat) : bool := same h a b.

  Module Box.
    Record box := { test : pred nat; size : nat }.
  End Box.

  Definition apply_test (b : Box.box) (n : nat) : bool := Box.test b n.

  Definition h : holder :=
    {| run := fun n => Nat.eqb n 0; same := Nat.eqb |}.

  Definition t1 : bool := apply_run h 0.
  Definition t2 : bool := apply_same h 2 2.
  Definition t3 : bool := apply_test {| Box.test := fun n => Nat.eqb n 1; Box.size := 1 |} 0.
End RecordFieldFunctionAlias.

Crane Extraction "record_field_function_alias" RecordFieldFunctionAlias.
