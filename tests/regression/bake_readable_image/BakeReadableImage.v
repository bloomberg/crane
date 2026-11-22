(* SPDX-License-Identifier: BSD-3-Clause *)
(** [Crane Bake]'s image as a reader of the generated file sees it: one row
    per node with a comment naming its constructor and fields, strings as
    C++ string literals, scoped enumerators by name.  The values cover what
    the comments and the text must spell: a rose tree whose children are a
    [crane::list] of boxed elements (the list's cells are nodes, and one
    list is the suffix of another: shared), strings with a quote, a
    backslash, control bytes and a hex digit after an escape, a negative
    [Z] and a negative float.  The program checks the values and that the
    shared suffix is one list again. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std Mapping.ZInt.
From Crane Require Extraction.
From Stdlib Require Import List ZArith.
From Corelib Require Import PrimString PrimInt63 PrimFloat.
Import ListNotations.

Crane Extract Inductive list =>
  "crane::list<%elem>"
  [ "crane::list<%elem>{}"
    "crane::cons(%a0, %a1)" ]
  "if (%scrut.empty()) { %br0 } else { const %t0& %b1a0 = %scrut.front(); auto %b1a1 = %scrut.tail(); %br1 }"
  Boxed Element "crane::box<%t0>"
  From "conslist.h".

Module BakeReadableImage.

Inductive color : Type := Red | Green | Blue.

Inductive rose : Type := Rose (label : PrimString.string) (shade : color) (kids : list rose).

Definition leaf (s : PrimString.string) (c : color) : rose := Rose s c [].

(** [shared] is all of ["a"]'s children and the tail of ["d"]'s. *)
Definition shared : list rose := [leaf "b" Green; leaf "c" Blue].
Definition forest : list rose :=
  [Rose "a" Red shared; Rose "d" Blue (leaf "e" Red :: shared)].

Definition odd_strings : list PrimString.string :=
  [ "say ""hi"""%pstring; "back\slash"%pstring;
    PrimString.cat (PrimString.make 1%uint63 1%uint63) "a"%pstring;
    PrimString.make 2%uint63 0%uint63 ].

Definition numbers : Z * PrimFloat.float := ((-42)%Z, (-0.25)%float).

Fixpoint labels (r : rose) : PrimString.string :=
  match r with
  | Rose s _ ks => fold_left (fun acc k => PrimString.cat acc (labels k)) ks s
  end.

Definition all_labels : PrimString.string :=
  fold_left (fun acc r => PrimString.cat acc (labels r)) forest ""%pstring.

Definition blue_count : nat :=
  let fix count (r : rose) : nat :=
    match r with
    | Rose _ c ks =>
      (match c with Blue => 1 | _ => 0 end) + fold_left (fun n k => n + count k) ks 0
    end in
  fold_left (fun n r => n + count r) forest 0.

Definition string_lengths : list PrimInt63.int := map PrimString.length odd_strings.

End BakeReadableImage.

Crane Bake BakeReadableImage.forest BakeReadableImage.odd_strings BakeReadableImage.numbers.

Crane Extraction "bake_readable_image" BakeReadableImage.
