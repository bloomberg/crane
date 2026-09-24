(* One component of a pair is erased in a destructuring binder, while the
   other survives.

     [=](std::pair<List<std::pair<T1, T2>>, std::any> x) mutable

   where the second component should be [List<T2>] -- Vellvm's h:74571, to
   the character.

   The bind's element types are spelled correctly and in full, twice, on the
   two lines above; only the lambda's parameter is wrong, and it is wrong
   component-wise.  So the type is in hand at the call and something reached
   into the pair and erased one side of it.

   A second, non-erroring instance sat in the same file:
   [List<std::pair<std::any, std::any>>::nil()], both components erased,
   which compiled only because [nil()] converts nothing.

   Both are fixed, and by one reading applied at two places: the position may
   fill what the term left open.  A custom constructor's erased type arguments
   are refined against the slot pointwise and at any depth, and a lambda
   binder's are refined against the domain the slot declares -- at the ML type
   rather than the C++ spelling, so the body decomposes the pair at the type
   it really has instead of unboxing at the erased view its own generation
   assumed.

   The import list is not harness configuration -- it selects the emission
   path.  Without the reified mapping the same term comes out through the
   class wrapper with a [const auto&] binder and no erasure at all, so a
   reduction and its control that agree on imports hold the variable that
   matters constant. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ExtLib Require Import Structures.Monad.

Import MonadNotation.
Local Open Scope monad_scope.

Inductive EOU (A : Type) : Type := | Ok : A -> EOU A | Err : nat -> EOU A.
Arguments Ok {A}.
Arguments Err {A}.

#[global] Instance EOU_monad : Monad EOU :=
  {| ret  := fun _ a => Ok a
   ; bind := fun _ _ m k => match m with Ok a => k a | Err c => Err c end |}.

Definition combine {A B : Type} (l : list B) : EOU (list (A * B) * list B) :=
  ret (nil, l).

Definition go {A B : Type} (a : A) (b : B) (l : list B)
  : EOU (list (A * B) * list B) :=
  bind (combine l) (fun x : list (A * B) * list B =>
    let (p, vargs) := x in
    ret (cons (a, b) p, vargs)).

Module PairComponentErasedInDestructuringBinder.
  Definition run := @go nat nat 1 2 (cons 3 nil).
End PairComponentErasedInDestructuringBinder.

Crane Extraction "pair_component_erased_in_destructuring_binder"
  PairComponentErasedInDestructuringBinder.
