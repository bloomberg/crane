(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*
   This test exposes the known issue mentioned in CLAUDE.md:
   "Inductives inside modules generate invalid C++"

   From translation.ml:352, inductives are always generated as namespaces (Dnspace).
   Inside a module (which becomes a struct in C++), this creates invalid
   namespace-inside-struct code.
*)
Require Import Crane.Mapping.NatInt.
Require Crane.Extraction.

Module InductiveInModule.

(* A module containing an inductive type *)
Module Inner.
  (* This inductive inside a module should generate invalid C++:
     a namespace inside a struct *)
  Inductive color : Type :=
  | Red : color
  | Green : color
  | Blue : color.

  Definition default_color := Red.

  Definition color_to_nat (c : color) : nat :=
    match c with
    | Red => 0
    | Green => 1
    | Blue => 2
    end.
End Inner.

(* Try to use the inner inductive *)
Definition test_color := Inner.color_to_nat Inner.Red.

(* Another variant: nested modules with inductives *)
Module Outer.
  Module Middle.
    Inductive option (A : Type) : Type :=
    | None : option A
    | Some : A -> option A.

    Arguments None {A}.
    Arguments Some {A} a.

    Definition get_or_default {A : Type} (default : A) (o : option A) : A :=
      match o with
      | None => default
      | Some x => x
      end.
  End Middle.

  Definition test_option := Middle.get_or_default 42 (Middle.Some 99).
End Outer.

Definition final_test := Outer.test_option.

End InductiveInModule.

Crane Extraction "inductive_in_module" InductiveInModule.
