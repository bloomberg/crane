(** [interp (case_ hl hr)] over a reified tree whose handlers return a
    concrete result: [handled_left] is 1, [handled_right] is 2.

    Fixed: the handlers are declared returning [ITree<T1>] at their erased
    index, and their bodies built [itree_ret(UINT64_C(1))], an
    [ITree<uint64_t>]: the branch value is at the index its match refined
    ([T1 = nat]), and C++ does not know the two are one type.  The value is
    now carried across with [crane_convert<T1>] where the position deduces
    its type ([itree_ret(%a0)] keeps the instantiation it is given). *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt Monads.ITreeReified.
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
