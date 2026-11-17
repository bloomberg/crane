(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A function of a module whose eponymous record is merged into its struct,
    not made a method -- its type names an inductive declared after the
    record -- takes the record, and is defined out of line.  There the
    record is spelled as the struct it is merged into is, by the struct's
    own qualifier: qualified by the struct as well, [Rq::Bag::Bag], it
    named the struct's constructor. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module RecordParamOutOfLine.
  Module Bag.
    Record bag := { size : nat; full : bool }.

    Inductive kind := Small | Large.

    Definition classify (b : bag) : kind := if full b then Large else Small.
  End Bag.

  Definition large : Bag.kind := Bag.classify {| Bag.size := 2; Bag.full := true |}.
End RecordParamOutOfLine.

Crane Extraction "record_param_out_of_line" RecordParamOutOfLine.
