(* Matching on a value whose type is a sum of event families.

   [sum1] is extracted to the empty string -- an event is erased wherever it
   appears -- so a match on an [(E +' F) X] scrutinee has no type to name its
   own alternatives at, and the generated dispatch reads

     if (std::holds_alternative<typename <T1<std::any>, T2<std::any>, T4>::Inl1>(ab.v())) {

   with the type name before the argument list missing entirely.

     error: type name requires a specifier or qualifier
     error: expected a qualified name after 'typename'

   In Vellvm this is 62 errors, all one construct: [Handler::case_] at
   vellvm_bench.h:2817. *)
From Crane Require Import Extraction.
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
