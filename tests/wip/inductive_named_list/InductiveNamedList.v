(* WIP: a user inductive named List collides with the runtime's List<T> template; the emitted C++ does not compile. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Module InductiveNamedList.
Inductive List : Type := LNil | LCons : nat -> List -> List.
Fixpoint len (l : List) : nat := match l with LNil => 0 | LCons _ r => S (len r) end.
Definition go : nat := len (LCons 1 (LCons 2 LNil)) + length (cons 1 nil).
End InductiveNamedList.
Crane Extraction "inductive_named_list" InductiveNamedList.
