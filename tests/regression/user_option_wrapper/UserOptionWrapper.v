(* Regression: a user-defined two-constructor wrapper mediating the recursion gets no
   iterative drain.

   [opt A] is [option] written out by hand: one nullary constructor and one
   unary.  The list-shaped check requires the second constructor to be
   [A -> g A -> g A], and the single-constructor wrapper case requires exactly
   one constructor, so this shape falls between them and gets nothing.

   Any user-defined enum-with-payload -- an error type, a tagged optional --
   has this shape, so it is not an exotic case. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module UserOptionWrapper.
Inductive opt (A : Type) : Type := non : opt A | so : A -> opt A.
Arguments non {A}. Arguments so {A} _.
Inductive t : Type := node : nat -> opt t -> t.
Definition wrap (k : nat) (acc : t) : t := node k (so acc).
Definition empty : t := node 0 non.
End UserOptionWrapper.
Crane Extraction "user_option_wrapper" UserOptionWrapper.
