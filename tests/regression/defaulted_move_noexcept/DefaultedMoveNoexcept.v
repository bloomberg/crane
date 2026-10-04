From Crane Require Import Mapping.Std.
From Crane Require Extraction.

Module DefaultedMoveNoexcept.

(** A recursive datatype gets a user-declared destructor, and so re-defaulted
    moves.  Their exception specification is inferred: [noexcept] exactly
    when moving the payload is. *)
Inductive seq (A : Type) := Nil | Cons (a : A) (s : seq A).
Arguments Nil {A}. Arguments Cons {A}.

Fixpoint len {A} (s : seq A) : nat :=
  match s with Nil => 0 | Cons _ r => S (len r) end.

End DefaultedMoveNoexcept.

Crane Extraction "defaulted_move_noexcept" DefaultedMoveNoexcept.
