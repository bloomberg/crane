(** Crane bug: a handler combinator polymorphic in the target family
    ([handle_intrinsic {E} (h : memE ~> stateT nat (itree E)) : intrE ~>
    stateT nat (itree E)]), applied to an unapplied subevent-polymorphic
    handler under a context that fixes the family ([on_mem : stateT nat
    (itree BotE) T -> ...]), is instantiated with the family [void].

    Observed (post-unapplied_subevent_handler install):
      return on_mem<T1>(handle_intrinsic<void, T1>(
          ... memM_interp<void, std::any>(...) ...
    unapplied_subevent_handler (the handler passed straight to [on_mem]) is
    fixed; one combinator in between still loses the family, which must
    come from [on_mem]'s parameter type through [handle_intrinsic]'s result.
    Diagnostics: [field has incomplete type 'void'], [argument may not have
    'void' type], [cannot form a reference to 'void'], [no matching
    function for call to 'trigger'].

    Reduced from Vellvm: [Handlers/Memory.v:94] [handle_intrinsic] and
    [Semantics/InterpretationStack.v:61] [on_mem], [fused_intrinsic := fun T
    e => on_mem (handle_intrinsic memM_interp e)].  The same shape recurs
    for every fused handler: [handle_global_debug], [handle_local_stack],
    [handle_local_debug], [handle_stack], [handle_memory], [fused_trigger]
    all come out [<_tcI0, void, ...>] -- the bulk of Vellvm's 60 errors. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree Events.State.
Import ITreeNotations.
Local Open Scope itree_scope.

Module HandlerCombinatorFamily.
  Variant memE : Type -> Type := Load : memE nat.
  Variant intrE : Type -> Type := Intr : intrE nat.
  Variant failE : Type -> Type := Fail : failE void.
  Variant noE : Type -> Type := .
  Definition BotE := failE +' noE.

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

  Definition out : itree BotE (nat * nat) := fused_intrinsic _ Intr 5.
  Definition is_five : bool :=
    match observe out with RetF (_, n) => Nat.eqb n 5 | _ => false end.
End HandlerCombinatorFamily.

Crane Extraction "handler_combinator_family" HandlerCombinatorFamily.
