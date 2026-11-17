(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a user definition named like a piece of Crane's runtime hides it
    in the generated code, which refers to the runtime without a leading
    [::].
    - An inductive named [crane] becomes a struct [crane] inside the
      module's struct, so [crane::small_vector] (or, under other options,
      [crane::shared_box], [crane::rc]) is looked up in it: "no template
      named 'small_vector' in 'UserNameHidesCraneRuntime::crane'".  Only a
      module named [crane] is renamed ([regression/module_named_crane]).
    - A definition named [crane_raw] hides the unqualified helper
      [crane_raw(p)] a loopified function calls on its children. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module UserNameHidesCraneRuntime.

Inductive crane := Cr : nat -> crane.

Inductive tree := Leaf | Node : tree -> nat -> tree -> tree.

Definition crane_raw (n : nat) : nat := n + 1.

Fixpoint sum (t : tree) : nat :=
  match t with Leaf => 0 | Node l x r => sum l + crane_raw x + sum r end.

Definition result : nat :=
  sum (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)) + match Cr 1 with Cr n => n end.

End UserNameHidesCraneRuntime.

Set Crane Loopify.
Crane Extraction "user_name_hides_crane_runtime" UserNameHidesCraneRuntime.
