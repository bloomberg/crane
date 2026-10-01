(* [interp (case_ hl hr)] over a reified tree whose handlers return a
   concrete result.

   Expected: [handled_left] is 1, [handled_right] is 2.
   Actual:   the handlers are written returning [ITree<crane::obj>] and their
             bodies build [ITree<uint64_t>]:
       error: no viable conversion from returned value of type
              'shared_ptr<ITree<unsigned long long>>' to function return type
              'shared_ptr<ITree<crane::obj>>' *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITreeReified.
From ITree Require Import ITree.

Variant AE : Type -> Type := A0 : AE nat.

Module CaseHandlerConcreteResult.
  Definition tl : itree (AE +' AE) nat := trigger (inl1 A0).
  Definition tr : itree (AE +' AE) nat := trigger (inr1 A0).

  Definition hl : AE ~> itree void1 := fun _ e => match e with A0 => Ret 1 end.
  Definition hr : AE ~> itree void1 := fun _ e => match e with A0 => Ret 2 end.

  Fixpoint result (fuel : nat) (t : itree void1 nat) : nat :=
    match fuel with
    | O => 0
    | S f =>
      match observe t with
      | RetF r => r
      | TauF t' => result f t'
      | VisF e _ => match e with end
      end
    end.

  Definition handled_left : nat := result 10 (interp (case_ hl hr) tl).
  Definition handled_right : nat := result 10 (interp (case_ hl hr) tr).
End CaseHandlerConcreteResult.

Crane Extraction "case_handler_concrete_result" CaseHandlerConcreteResult.
