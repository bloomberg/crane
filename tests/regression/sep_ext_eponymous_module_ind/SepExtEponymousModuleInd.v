From Crane Require Extraction.
From Crane Require Import Mapping.Std.

Module Trie.
  Inductive trie (A : Type) : Type :=
  | Leaf
  | Branch (t : option A) (t0 t1 : trie A).
End Trie.

Module UseTrie.
  Import Trie.
  Definition memo := trie (option nat).
End UseTrie.

Crane Separate Extraction UseTrie.
