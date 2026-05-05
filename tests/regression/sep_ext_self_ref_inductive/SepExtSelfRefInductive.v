From Crane Require Extraction.
From Crane Require Import Mapping.Std.

Module Type S.
  Parameter t : Type.
End S.

Module HashTrie (X : S).
  Inductive Trie (V : Type) :=
    | Empty
    | Node (k : X.t) (v : V) (left : Trie V) (right : Trie V).

  Definition empty {V : Type} : Trie V := @Empty V.
  Definition is_empty {V : Type} (t : Trie V) : bool :=
    match t with @Empty _ => true | _ => false end.
End HashTrie.

Crane Separate Extraction HashTrie.
