(* A [Vis] stores its event as a thunk, and an injection into a sum names no
   type at the trigger, so [itree_vis] used to unwrap [inl1 e] and [inr1 e]
   both to [e]: the side was gone, and a match on the event at its sum type
   threw [bad_any_cast].  Where both summands are the same type the side is
   the only thing that tells the two events apart.

   Expected: the match reads [inl1] as 1 and [inr1] as 2.
   Before:   [std::bad_any_cast] from [crane_event_as<Sum1<AE, AE, ...>>]. *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITreeReified.
From ITree Require Import ITree.

Variant AE : Type -> Type := A0 : AE nat.

Module SumSideSurvivesVis.
  Definition tl : itree (AE +' AE) nat := trigger (inl1 A0).
  Definition tr : itree (AE +' AE) nat := trigger (inr1 A0).
  Definition vr : itree (AE +' AE) nat := Vis (inr1 A0) (fun n => Ret n).

  Definition side {X : Type} (e : (AE +' AE) X) : nat :=
    match e with inl1 _ => 1 | inr1 _ => 2 end.

  Definition first_side (t : itree (AE +' AE) nat) : nat :=
    match observe t with
    | VisF e _ => side e
    | _ => 0
    end.

  Definition left_side : nat := first_side tl.
  Definition right_side : nat := first_side tr.
  Definition right_vis : nat := first_side vr.
End SumSideSurvivesVis.

Crane Extraction "sum_side_survives_vis" SumSideSurvivesVis.
