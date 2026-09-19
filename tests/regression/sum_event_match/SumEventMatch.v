(* Matching on a value whose type is a sum of event families.

   An event is erased wherever it appears, but a scrutinee is not: a match on
   an [(E +' F) X] still needs a type to name its alternatives at, and a
   function taking one still needs a parameter type.  [sum1] therefore has a
   real C++ representation, [Sum1] in [crane_itree.h], shaped like any other
   Crane variant so that the ordinary match dispatch applies to it unchanged.

   Two things this pins down.  A custom mapping that names a template without
   saying where its arguments go -- ["Sum1"] rather than ["Sum1<%t0, %t1>"] --
   takes them after it, and every printer of a custom type agrees on that; a
   type spelled [Sum1<AE, BE, T1>] in a body and [Sum1] in the signature is
   two types.  And [sum1_inl] / [sum1_inr] defer deduction of the other
   summand the way [itree_trigger] already does, so a constructor applied on
   its own still knows what sum it belongs to.

   In Vellvm this was 62 errors, all one construct: [Handler::case_]. *)From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.

Variant AE : Type -> Type := A0 : AE nat.
Variant BE : Type -> Type := B0 : BE nat.

Definition handle {X : Type} (e : (AE +' BE) X) : itree (AE +' BE) X :=
  match e with
  | inl1 a => trigger (inl1 a)
  | inr1 b => trigger (inr1 b)
  end.

Module SumEventMatch.
  Definition use : itree (AE +' BE) nat := handle (inl1 A0).
End SumEventMatch.

Crane Extraction "sum_event_match" SumEventMatch.
