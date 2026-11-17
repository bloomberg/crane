(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A file-scope inductive [tree], spelled [Tree], in a separate extraction
    whose other file [NestedLib] nests a struct [Tree] inside [Sub].  That
    nested struct shadows nothing in this file, so this file's [Tree] is
    written as it is, not qualified for global scope. *)

From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.
From CraneTestsRegression Require sep_ext_nested_struct_name.NestedLib.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree.

Fixpoint depth (t : tree) : nat :=
  match t with Leaf => 0 | Node t' _ => S (depth t') end.

Definition sample : tree := Node (Node Leaf 1) 2.

Definition total : nat :=
  depth sample + NestedLib.Sub.size (NestedLib.Sub.Node NestedLib.Sub.Leaf 0 NestedLib.Sub.Leaf).

Crane Separate Extraction total.
