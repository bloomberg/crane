From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.

(** A method its struct only declares, defined after the struct, is
    loopified as one defined inside it.
    [tree] and [forest] are a mutual group at the top level, so a member
    naming a struct of the group is written after the whole group: [depth],
    a method of [tree], is declared in [Tree] and defined after it.  Loopify
    transformed the methods it found in the struct and never looked at a
    definition written out of line, so [depth] kept recursing in C++, one
    stack frame per node, though every other method of the struct was a
    loop.  A million nodes overflow the stack without the fix. *)
Inductive tree : Set :=
| Leaf : tree
| Node : forest -> tree -> tree
with forest : Set :=
| Bare : forest
| Grove : tree -> forest -> forest.

Fixpoint depth (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node _ r => depth r + 1
  end.

Crane Extraction "loopify_out_of_line_method" tree forest depth.
