(* A polymorphic helper whose event argument is absurd ([FailE void]) gets
   promoted to a method on the event struct.  Three things have to survive the
   move into the struct:

   - the template parameters the body names, not only the ones the signature
     spells -- the result of a trigger is an index of the event type, so a
     local declared at it has no other spelling;
   - the receiver's position, counted among the arguments C++ is passed rather
     than among the arrows of the ML type: the erased [FailE -< E] instance
     separates the two;
   - the itree extraction mode, which is read off the codomain and so is the
     same whether the function stays at top level or becomes a method --
     otherwise the [bind] is desugared sequentially into the signature of a
     function that returns a tree.

   Binding the trigger directly is the case where neither side can name the
   response type: [itree_bind] takes it from the continuation, and a
   continuation written generically -- what an absurd response leaves -- is
   handed the boxed response as it stands.

   In Vellvm this is the [raise]/[raiseUB] cluster, 40 errors, from
   rocq/Semantics/LLVMEvents.v:176-193 via Utils/ITreeUtil.v:6. *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.
From Stdlib Require Import List.
Import ListNotations.

Variant FailE : Type -> Type := Throw : unit -> FailE void.

Definition cast' {E : Type -> Type} {A : Type} `{FailE -< E} (e : FailE void)
  : itree E A :=
  ITree.bind (trigger e) (fun v : void => match v with end).

Definition raise {E} {A} `{FailE -< E} (n : nat) : itree E A :=
  cast' (Throw tt).

Module PromotedMethodLeaksParam.
  Definition use (l : list nat) : itree FailE nat :=
    match l with
    | [] => raise 0
    | x :: _ => Ret x
    end.
End PromotedMethodLeaksParam.

Crane Extraction "promoted_method_leaks_param" PromotedMethodLeaksParam.
