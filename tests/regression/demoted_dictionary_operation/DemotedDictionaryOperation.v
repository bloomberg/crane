(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A mapped operation taking a dictionary of a class the unit demotes to a
    struct.  [tag_of] computes a [Tag] from data, so [Tag] is a struct here
    and a generic caller holds its dictionary as a value.  The operation's
    text names no dictionary, so a call passes none: passed, it would be
    what [%arg(x)] binds, and every later argument would shift by one. *)

From Stdlib Require Import List.
From Crane Require Import Extraction Mapping.NatInt.
From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp Crane.Cpp.
Import PrimString.PStringNotations ListNotations.

Module DemotedDictionaryOperation.

(** A class of the shape of [ST.Code]: a number for a type. *)
Class Tag (A : Type) : Type := { tag : nat }.
Arguments tag A {Tag}.

(** A tag computed from data: [Tag] is data in this unit. *)
#[global] Instance tag_of (n : nat) : Tag nat := {| tag := n |}.

(** [x - y]: order-sensitive, and blind to its dictionary. *)
Axiom sub : forall {A : Type} `{Tag A}, nat -> nat -> nat.

#[global] Instance sub_mapping : OperationMapping (Ref (@sub)) :=
  (pure_cpp [] ["x"; "y"] (Expr "%arg(x) - %arg(y)"))%pstring.

(** Generic over the dictionary, which it holds as a value. *)
Definition diff {A : Type} `{Tag A} (x y : nat) : nat := sub (A:=A) x y.

(** The dictionary read as data, next to the operation. *)
Definition diff_plus_tag {A : Type} `{Tag A} (x y : nat) : nat :=
  sub (A:=A) x y + tag A.

Definition seven : nat := @diff nat (tag_of 100) 10 3.
Definition seventeen : nat := @diff_plus_tag nat (tag_of 10) 10 3.

End DemotedDictionaryOperation.

Crane Extraction "demoted_dictionary_operation" DemotedDictionaryOperation.
