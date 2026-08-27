(* WIP: non-uniform (nested) inductive with a list A recursive occurrence; the emitted C++ template does not instantiate. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Module NonUniformListNest.
Inductive n2 (A : Type) : Type := Z2 : A -> n2 A | S2 : n2 (list A) -> n2 A.
Arguments Z2 {A} _.
Arguments S2 {A} _.
Fixpoint depth (A : Type) (x : n2 A) : nat := match x with Z2 _ => 0 | S2 y => S (depth (list A) y) end.
Definition go : nat := depth nat (S2 (Z2 (cons 1 nil))).
End NonUniformListNest.
Crane Extraction "non_uniform_list_nest" NonUniformListNest.
