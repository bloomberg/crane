(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a loopified function over a tree with a field
    [(nat * option tree)] -- [Mapping.Std]'s [std::pair] of a
    [std::optional] -- does not compile.  The continuation frame saves the
    [option tree] bound out of the pair, an [std::optional<tree>], but
    types the frame field at the storage type of a recursive field,
    [std::optional<std::shared_ptr<tree>>]: "no viable conversion", and then
    a [std::shared_ptr<tree>] read where a [tree] is wanted.  An [option
    tree] field alone, or a pair alone, is fine, as is either without
    loopification. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module LoopifyPairOptionChild.

Inductive tree := Leaf | Node : tree -> (nat * option tree) -> tree.

Fixpoint sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l (x, o) => sum l + x + match o with Some u => sum u | None => 0 end
  end.

Definition result : nat := sum (Node Leaf (1, Some (Node Leaf (2, None)))).

End LoopifyPairOptionChild.

Set Crane Loopify.
Crane Extraction "loopify_pair_option_child" LoopifyPairOptionChild.
