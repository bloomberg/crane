From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Stdlib Require Import Vector Fin.

(** [Vector.nth] eliminates the vector under a motive [Fin.t n -> A] and then
    applies the result to the index.  The generated match keeps the motive's
    arrow as the lambda's declared return type, [std::function<T1(T)>], while
    each branch returns a [T1] -- so the extra argument is consumed twice in
    the type and once in the term. *)

Module DependentVectorNth.

  Definition v : Vector.t nat 3 :=
    Vector.cons _ 1 _ (Vector.cons _ 2 _ (Vector.cons _ 3 _ (Vector.nil _))).

  Definition run : nat :=
    Vector.nth v (Fin.FS Fin.F1) + Vector.fold_left Nat.add 0 v.

End DependentVectorNth.

Crane Extraction "dependent_vector_nth" DependentVectorNth.
