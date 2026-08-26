(* Regression: recursion nested inside a [Record] gets no iterative drain.

   [Record cell (A : Type) := mkc { hd : nat ; tl : A }] is a plain
   single-constructor wrapper, but it is registered as a record rather than an
   inductive, and the drain classifier's wrapper case does not cover it.
   Destroying [more (mkc k acc)] chains recurses through [~cell<t>].

   Compare the mutual-inductive spelling of the same shape, which does get a
   drain -- so this is specifically about [Record]. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module RecordMediatedDrain.
Record cell (A : Type) : Type := mkc { hd : nat ; tl : A }.
Arguments mkc {A} _ _. Arguments hd {A} _. Arguments tl {A} _.
Inductive t : Type := stop : t | more : cell t -> t.
Definition wrap (k : nat) (acc : t) : t := more (mkc k acc).
Definition empty : t := stop.
End RecordMediatedDrain.
Crane Extraction "record_mediated_drain" RecordMediatedDrain.
