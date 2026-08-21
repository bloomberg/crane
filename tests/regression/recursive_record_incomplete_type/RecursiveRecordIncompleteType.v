From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Module RecursiveRecordIncompleteType.

(** A record-shaped inductive whose recursion runs through a [list]. Written
    as [Inductive] with named fields rather than [Record], since Rocq rejects
    recursive [Record]s outright.

    Crane translates record-shaped inductives to a plain struct with the
    fields inlined as members, which is right for non-recursive records but
    wrong here: the [kids] member came out as [List<cell> kids;] inside
    [struct cell], i.e. the struct used by value in its own definition,
    before its closing brace -- an incomplete type, which does not compile.

    Record classification now declines self-referential types, so [cell] gets
    the standard inductive representation, which puts the recursive
    occurrence behind a smart pointer. The occurrence is looked for anywhere
    in a field's type: reaching [cell] through [list] leaves the struct just
    as incomplete as a bare [cell] field would. *)
Inductive cell : Type := MkCell { key : nat; kids : list cell }.

Fixpoint csum (c : cell) : nat :=
  key c + (fix go (l : list cell) : nat :=
             match l with [] => 0 | x :: r => csum x + go r end) (kids c).

Definition run (n : nat) : nat :=
  let ks := [MkCell n []; MkCell (S n) []; MkCell (S (S n)) []] in
  let a := csum (MkCell 1 ks) in
  let b := csum (MkCell 2 ks) in
  a + b.

End RecursiveRecordIncompleteType.

Crane Extraction "recursive_record_incomplete_type" RecursiveRecordIncompleteType.
