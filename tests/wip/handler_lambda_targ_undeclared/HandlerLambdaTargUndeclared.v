(** An eta-expanded handler, inside a definition parameterised by a
    typeclass, passed to a combinator that applies it as a rank-2
    natural transformation.  Reduced from Vellvm's
    Semantics/InterpretationStack.v:60-90 (fused_local and siblings).

    Fixed since filing: the lambda no longer names an undeclared [T2] (the
    eta site binds the index, as [crane::obj] where nothing deduces it), and
    [handle_local_debug]'s body, [Ret (s, s + width)] at the index its match
    refined, is converted at [T2] ([itree_ret(std::make_pair(s,
    crane_convert<T2>(...)))]).

    Open (diagnosed 2026-11-24): [handle_local_stack]'s [h T e].  [h]'s Rocq
    type [LocalE ~> stateT lenv (itree E)] quantifies [T] inside a parameter
    type, so its Core type erases the quantified variable to [Unknown], and
    [Unknown] unifies with anything: extraction records no coercion where
    [h T e : stateT lenv (itree E) Unknown] meets [T].  [h] is a deduced
    [F0 &&], and the eta lambda the caller passes returns
    [stateT<lenv, itree_tc, crane::obj>]; the body [return h(e);] needs
    [crane_convert<stateT<lenv, itree_tc, T2>>(h(e))] ([crane_cast_to] for
    [crane::fn] converts the result).  Nothing on the consumer side asks: no
    Core coercion, and the typed-fit/[Coerce.decide] pair is skipped because
    the slot names a type variable.  Making [decide] convert a box inside a
    mapped type to a concrete type was tried and is too broad (dozens of
    typed-fit failures across regression: pairs, lists and event-only
    mismatches C++ resolves); the decision needs the Core fact that the
    callee is a parameter of rank-2 type applied at a type, which Core does
    not keep.  The same layer is open in mrec_ctx_wrapped_in_ret
    ([ctx0(d)]) and eta_handler_event_as_template ([crane::apply2(h, e,
    s)]). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.
From ExtLib Require Import Structures.Monads.
Import ITree.Basics.Basics.Monads.

Variant LocalE : Type -> Type := | LGet : LocalE nat.
Definition lenv := nat.
Definition Big := (nat * nat)%type.

Class Params := { width : nat }.

Section S.
  Context {Pa : Params}.
  Context {E : Type -> Type}.

  Definition handle_local_debug : LocalE ~> stateT lenv (itree E) :=
    fun _ e => match e in LocalE T return stateT lenv (itree E) T with
               | LGet => fun s => Ret (s, s + width)
               end.

  Definition handle_local_stack (h : LocalE ~> stateT lenv (itree E))
    : LocalE ~> stateT lenv (itree E) := fun T e => h T e.

  Definition on_ls {T} (c : stateT lenv (itree E) T) : stateT Big (itree E) T :=
    fun b => ITree.bind (c (fst b)) (fun sa => Ret ((fst sa, snd b), snd sa)).
End S.

Section T.
  Context {Pa : Params}.

  Definition fused_local : LocalE ~> stateT Big (itree LocalE) :=
    fun T e => on_ls (handle_local_stack handle_local_debug T e).

  Definition use (n : nat) : itree LocalE (Big * nat) := fused_local _ LGet (n, n).
End T.

Module HandlerLambdaTargUndeclared.
  Definition go `{Params} (n : nat) := use n.
End HandlerLambdaTargUndeclared.

Crane Extraction "handler_lambda_targ_undeclared" HandlerLambdaTargUndeclared.
