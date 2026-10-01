From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
Import ListNotations.
From CraneTestsRegression Require Import modtype_in_wrapper_named_bare.AstLib.

(** The functor parameter names the module type bare. *)
Module Make (X : AstLib.Ord).
  Definition tbl (elt : Set) : Set := list (X.t * elt).
  Definition empty (elt : Set) : tbl elt := [].
End Make.
