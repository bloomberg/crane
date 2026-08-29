From Stdlib Require Import Lists.List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ModuleInductiveSameName.
  (** A submodule containing an inductive of the same name.  Both become C++
      members named [Color] inside the enclosing struct: [member 'Color' has
      the same name as its class]. *)
  Module Color.
    Inductive Color := R | G.
    Definition v (c : Color) := match c with R => 1 | G => 2 end.
  End Color.

  Definition run (k : nat) : nat := Color.v Color.R + k.
End ModuleInductiveSameName.

Crane Extraction "module_inductive_same_name" ModuleInductiveSameName.
