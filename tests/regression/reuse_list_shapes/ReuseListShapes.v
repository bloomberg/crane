(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Perceus reuse over the Stdlib's own lists, under the options Vellvm
    extracts with: [combine] walks a second list beside the one it consumes
    and builds pairs, so neither input's cells fit its output; [firstn]
    counts down a [nat] beside its list; [list]'s tail field is named [l];
    and a match on a local copied out of a record field rebuilds through
    that local. *)

From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module ReuseListShapes.

Definition zipped : list (nat * nat) := combine [1; 2; 3] [10; 20; 30; 40].
Definition firsts : list nat := firstn 2 [5; 6; 7].

Fixpoint bump (l : list nat) : list nat :=
  match l with [] => [] | x :: t => S x :: bump t end.

Inductive frames := Single : list nat -> frames | Push : list nat -> frames -> frames.
Record mem := { stack : frames; top : nat }.

Definition add_to_frame (m : mem) (k : nat) : frames :=
  let s := stack m in
  match s with
  | Single f => Single (k :: f)
  | Push f rest => Push (k :: f) rest
  end.

Definition result : nat :=
  fold_left (fun acc '(a, b) => acc + a + b) zipped 0
  + fold_left Nat.add firsts 0
  + fold_left Nat.add (bump [1; 2]) 0
  + match add_to_frame {| stack := Push [1] (Single [2]); top := 0 |} 7 with
    | Push f _ => fold_left Nat.add f 0
    | Single _ => 0
    end.

End ReuseListShapes.

Set Crane NonAtomicRc.
Set Crane Reuse.
Set Crane BoxedFields.
Set Crane FastVariant.
Crane Loopify combine firstn ReuseListShapes.bump.
Crane Extraction "reuse_list_shapes" ReuseListShapes.
