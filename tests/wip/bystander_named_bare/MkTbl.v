From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
Import ListNotations.
From CraneTestsWIP Require Import bystander_named_bare.Ord.

Module Make (X : Ord).
  Definition tbl (elt : Set) : Set := list (X.t * elt).
  Definition empty (elt : Set) : tbl elt := [].
End Make.
