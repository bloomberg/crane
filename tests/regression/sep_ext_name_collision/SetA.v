From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

(* Both SetA and SetB define a function called 'make'.
   Without namespaces these would collide in C++.
   With namespaces: SetA::make and SetB::make are distinct. *)

Definition make (n : nat) : nat := n + 1.

Crane Separate Extraction make.
