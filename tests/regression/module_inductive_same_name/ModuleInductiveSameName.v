From Stdlib Require Import Lists.List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ModuleInductiveSameName.
  (** A submodule containing an inductive of the same name.  A C++ member may
      not share its enclosing class's name, so the module is emitted as
      [struct Color_Mod] holding [enum class Color]. *)
  Module Color.
    Inductive Color := R | G.
    Definition v (c : Color) := match c with R => 1 | G => 2 end.
  End Color.

  Definition run (k : nat) : nat := Color.v Color.R + k.
End ModuleInductiveSameName.

Crane Extraction "module_inductive_same_name" ModuleInductiveSameName.
