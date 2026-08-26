(* WIP: a Rocq module named std produces a C++ namespace std, which collides with the standard library. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module ModuleNamedStd.
Module std. Definition x : nat := 1. End std.
Definition go : nat := std.x.
End ModuleNamedStd.
Crane Extraction "module_named_std" ModuleNamedStd.
