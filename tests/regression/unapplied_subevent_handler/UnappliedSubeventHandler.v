(** Crane bug: a handler polymorphic in its target family through a
    subevent constraint ([memM_interp {E} `{failE -< E} : memE ~> stateT
    nat (itree E)]), passed *unapplied* where the family is fixed
    ([on_mem : (memE ~> stateT nat (itree BotE)) -> ...]), is instantiated
    with the family written as [void].

    Observed (post-itree_interp_state HEAD):
      return memM_interp<void, std::any>(...)
    The family should be [BotE] (= [Sum1<FailE, NoE, std::any>]).  Also
    present in the same expression: the [ReSum_id] eta lambda of
    resum_id_eta_lambda ([no matching function for call to 'ReSum_id']),
    which Vellvm does hit through this path.

    Reduced from Vellvm, [Semantics/InterpretationStack.v]
    [fused_intrinsic := fun T e => on_mem (handle_intrinsic memM_interp e)]:
    once interp_state is real, instantiating [interp_vellvm_h] produces
    [Memory2::template memM_interp<_tcI0, void, std::any>(...)] and a
    cascade through [Monad_itree<void>] ([field has incomplete type
    'void'], [argument may not have 'void' type], [std::any_cast<void>],
    [trigger_cast_] in raiseOOM/raiseUB/raise), about 40 of the ~50
    errors behind the interp_state handler. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree Events.State.
Import ITreeNotations.
Local Open Scope itree_scope.

Module UnappliedSubeventHandler.
  Variant memE : Type -> Type := Load : memE nat.
  Variant failE : Type -> Type := Fail : failE void.
  Variant noE : Type -> Type := .
  Definition BotE := failE +' noE.

  (* Vellvm's Memory.memM_interp: a handler polymorphic in its target
     family through a subevent constraint. *)
  Definition memM_interp {E} `{failE -< E} : memE ~> Monads.stateT nat (itree E) :=
    fun _ e s => match e with Load => if Nat.eqb s 0 then v <- trigger Fail ;; match v : void with end
                                      else Ret (s, s) end.

  (* Vellvm's InterpretationStack.on_mem / fused_intrinsic: the handler is
     passed unapplied at the concrete family. *)
  Definition on_mem (h : memE ~> Monads.stateT nat (itree BotE)) : memE ~> Monads.stateT nat (itree BotE) := h.
  Definition fused : memE ~> Monads.stateT nat (itree BotE) := fun T e => on_mem memM_interp T e.

  Definition out : itree BotE (nat * nat) := fused _ Load 5.
  Definition is_five : bool :=
    match observe out with RetF (_, n) => Nat.eqb n 5 | _ => false end.
End UnappliedSubeventHandler.

Crane Extraction "unapplied_subevent_handler" UnappliedSubeventHandler.
