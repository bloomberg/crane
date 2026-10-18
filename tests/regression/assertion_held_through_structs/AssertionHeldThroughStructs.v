(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A module type and a class whose concepts name a type of the outermost
    module, so that module's struct holds back every assertion of them
    until both concepts are declared after it: one of a module nested two
    structs deep, one of a module and one of an instance nested three deep.
    Each assertion names its subject from where it is finally written,
    qualified by every struct it left. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import NatIntStd.

Module AssertionHeldThroughStructs.

Definition key := nat.

Module Type STORE.
  Parameter lookup : key -> nat.
End STORE.

Class HasK (A : Type) := { getk : A -> key }.

Module Mid.
  Module S : STORE.
    Definition lookup (k : key) : nat := k + 1.
  End S.
  Module Inner.
    Module S2 : STORE.
      Definition lookup (k : key) : nat := k + 2.
    End S2.
    #[export] Instance hk : HasK nat := { getk := fun n => n }.
  End Inner.
  Definition run : nat := S.lookup 1 + Inner.S2.lookup 2 + @getk nat Inner.hk 3.
End Mid.

End AssertionHeldThroughStructs.

Crane Extraction "assertion_held_through_structs" AssertionHeldThroughStructs.Mid.run.
