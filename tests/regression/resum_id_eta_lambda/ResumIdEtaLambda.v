(** Crane bug: under [case_] of unapplied subevent-polymorphic handlers,
    the [ReSum_id] dictionary argument ([Id_ IFun]) is emitted as a
    two-parameter lambda where [Id_<obj, C>] is a one-argument function.

    Observed (86aac86af):
      CategoryOps::template ReSum_id<std::any, std::function<std::any(std::any)>>(
          [](std::any, const auto &eta0_) { return Function::Id_IFun(eta0_); },
          std::any())
    [Id_ obj C := forall a : obj, C a a]: the slot is
    [std::function<std::function<std::any(std::any)>(std::any)>], so the
    lambda must take the (erased) object only and return the IFun, as it
    does when [fused_trigger] is applied directly:
      [](std::any) { return crane_erase_fn<std::any>(Function::Id_IFun); }
    Here the handler is passed unapplied to [case_], and the eta-expanded
    IFun argument is folded into the dictionary lambda's parameters.
    Diagnostic:
      error: no matching function for call to 'ReSum_id'

    Reduced from Vellvm, [Semantics/InterpretationStack.v]
    [interp_vellvm_h := case_ (fused_trigger (F := ExternalCallE)) (case_ ...)]
    with [fused_trigger {F} `{F -< MCFGEbot} := fun _ e s => r <- trigger e;; ret (s, r)]:
    found behind Vellvm's interp_mcfg error on 86aac86af. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.
Import ITreeNotations.
Local Open Scope itree_scope.

Module ResumIdEtaLambda.
  Definition stateT (S : Type) (M : Type -> Type) (A : Type) : Type := S -> M (prod S A).

  Class Params : Type := { ptr : Type ; zero : ptr }.

  Section WithParams.
    Context {Pa : Params}.
    Variant aE : Type -> Type := A : ptr -> aE nat.
    Variant bE : Type -> Type := B : bE nat.
    Variant cE : Type -> Type := C : cE nat.
    Definition BotE := aE +' bE +' cE.

    (* Vellvm's InterpretationStack.fused_trigger *)
    Definition fused_trigger {F} `{F -< BotE} : forall T, F T -> stateT nat (itree BotE) T :=
      fun _ e s => r <- trigger e ;; Ret (s, r).

    (* Vellvm's interp_vellvm_h: case_ over fused_triggers, unapplied. *)
    Definition h : aE +' bE +' cE ~> stateT nat (itree BotE) :=
      case_ (fused_trigger (F := aE)) (case_ (fused_trigger (F := bE)) (fused_trigger (F := cE))).
    Definition use_c (s : nat) : itree BotE (nat * nat) := h _ (inr1 (inr1 C)) s.
  End WithParams.

  #[global] Instance natParams : Params := { ptr := nat ; zero := 0 }.

  Definition is_cc : bool :=
    match observe (use_c 1) with
    | VisF e _ => match e with inr1 (inr1 C) => true | _ => false end
    | _ => false
    end.
End ResumIdEtaLambda.

Crane Extraction "resum_id_eta_lambda" ResumIdEtaLambda.
