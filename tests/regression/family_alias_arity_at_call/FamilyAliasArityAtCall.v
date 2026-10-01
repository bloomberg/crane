(** Crane bug: a family alias with promoted parameters written as an
    explicit *family* argument is missing its trailing index argument.

    Observed (post-handler_combinator_family install):
      template <typename ptr, typename x> using BotE = Sum1<ExtE<ptr>, FailE, x>;
      ...
      return on_mem<_tcI0, T1>(handle_intrinsic<BotE<typename _tcI0::ptr>, T1>(
          ... memM_interp<BotE<typename _tcI0::ptr>, std::any>(...) ...
    [BotE] takes [ptr] and the index [x]; as a family it must be written
    [BotE<typename _tcI0::ptr, std::any>] (as it is elsewhere, e.g.
    [Monad_itree<MCFGEbot<ptr, iptr, std::any>>]).  Diagnostic:
      error: too few template arguments for alias template 'BotE'
    handler_combinator_family (the family without promoted parameters,
    written [BotE<std::any>]) passes.  Compile-only (a top-level [observe]
    match at the concrete instance hits a separate, known spelling issue).

    Reduced from Vellvm: [Memory2::template handle_intrinsic<_tcI0,
    MCFGEbot<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>, T1>(...)]
    -- 8 of Vellvm's 14 remaining errors. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree Events.State.
Import ITreeNotations.
Local Open Scope itree_scope.

Module FamilyAliasArityAtCall.
  Class Params : Type := { ptr : Type ; zero : ptr }.
  Variant memE : Type -> Type := Load : memE nat.
  Variant intrE : Type -> Type := Intr : intrE nat.
  Variant failE : Type -> Type := Fail : failE void.
  Section WithParams.
  Context {Pa : Params}.
  Variant extE : Type -> Type := Ext : ptr -> extE unit.
  Definition BotE := extE +' failE.

  Definition memM_interp {E} `{failE -< E} : memE ~> Monads.stateT nat (itree E) :=
    fun _ e s => match e with Load => if Nat.eqb s 0 then v <- trigger Fail ;; match v : void with end
                                      else Ret (s, s) end.

  (* Vellvm's Handlers/Memory.v:94 [handle_intrinsic {E} (h : memM ~> stateT state (itree E))
     : IntrinsicE ~> stateT state (itree E) := fun T e => h _ (handle_intrinsicM e)]. *)
  Definition handle_intrinsic {E} (h : memE ~> Monads.stateT nat (itree E))
    : intrE ~> Monads.stateT nat (itree E) :=
    fun T e => match e in intrE T return Monads.stateT nat (itree E) T with Intr => h _ Load end.

  (* InterpretationStack.v:61 [on_mem] and [fused_intrinsic := fun T e => on_mem (handle_intrinsic memM_interp T e).. *)
  Definition on_mem {T} (f : Monads.stateT nat (itree BotE) T) : Monads.stateT nat (itree BotE) T := f.
  Definition fused_intrinsic : intrE ~> Monads.stateT nat (itree BotE) :=
    fun T e => on_mem (handle_intrinsic memM_interp T e).

  End WithParams.
  #[global] Instance natParams : Params := { ptr := nat ; zero := 0 }.
  Definition out : itree BotE (nat * nat) := fused_intrinsic _ Intr 5.
End FamilyAliasArityAtCall.

Crane Extraction "family_alias_arity_at_call" FamilyAliasArityAtCall.
