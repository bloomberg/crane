(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A record merged into its module's struct, the record of no parameters:
    the struct is no class template, but a function of the module was
    spelled as one of a template struct's, [Bag<>::zero], which does not
    parse.  So was every use of a second inductive's recursor the module
    declares, [Bag<>::template kind_rect<T1>]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module RecordModuleFunctionQualifier.
  Module Bag.
    Record bag := { size : nat; full : bool }.

    Inductive kind := Small | Large.

    Definition zero : nat := 0.

    Definition pick {A : Type} (b : bag) (x y : A) : A := if full b then x else y.

    Definition classify (k : kind) : nat := match k with Small => 1 | Large => 2 end.
  End Bag.

  Definition empty : Bag.bag := {| Bag.size := Bag.zero; Bag.full := false |}.

  Definition picked : nat := Bag.pick empty 3 4.

  Definition large : nat := Bag.classify Bag.Large.
End RecordModuleFunctionQualifier.

Crane Extraction "record_module_function_qualifier" RecordModuleFunctionQualifier.
