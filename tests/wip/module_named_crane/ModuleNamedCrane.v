(* WIP: a Rocq module named crane produces a C++ namespace crane, which collides with the Crane runtime namespace. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module ModuleNamedCrane.
Module crane. Definition x : nat := 2. End crane.
Definition go : nat := crane.x.
End ModuleNamedCrane.
Crane Extraction "module_named_crane" ModuleNamedCrane.
