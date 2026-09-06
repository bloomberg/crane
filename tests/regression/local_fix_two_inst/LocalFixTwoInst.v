(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A [let fix] that is polymorphic in its element type and is instantiated at
    two different types in the same body.  The local fixpoint is emitted
    monomorphically, so the second instantiation does not type-check. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import List.
Import ListNotations.

Module LocalFixTwoInst.
Definition run : nat :=
  let fix len (A : Type) (l : list A) : nat :=
      match l with [] => 0 | _ :: r => S (len A r) end in
  len nat [1;2;3] + len bool [true;false].
End LocalFixTwoInst.

Crane Extraction "local_fix_two_inst" LocalFixTwoInst.run.
