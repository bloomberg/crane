(** A natural transformation passed as a *higher-order argument* is
    eta-expanded into a generic lambda whose parameter type spells the event
    family as a template -- but an erased event family is emitted as a plain
    non-template type, so the lambda does not parse.

    [AE] is emitted as [enum class AE { A0 };], yet the call site writes

      run<T1, T2>([]<typename _T2>(const AE<_T2> &a0) -> decltype(auto) {
                    return base<_T2, std::invoke_result_t<decltype(a0)&, _T2&>>(a0);
                  }, e);

    giving

      error: expected ')'
      error: use of undeclared identifier 'a0'

    Expected: the eta-expanded parameter is [const AE& a0], since the index is
    erased from the event type, with [_T2] used only where the index survives.

    Negative result worth keeping: if the handler's domain is a genuine type
    constructor rather than an erased event -- e.g. [Definition memM (T : Type)
    := nat -> T.], which is emitted as [template <typename t> using memM =
    ...] -- then [memM<_T2>] is well-formed and the same program compiles. So
    the defect is specifically the erased-event case, not eta-expansion in
    general.

    Vellvm has the same construct at [vellvm_bench.h:19306], [:19318] and
    [:19328] via [src/rocq/Semantics/InterpretationStack.v:79]:

      Definition fused_intrinsic : IntrinsicE ~> stateT FusedS (itree MCFGEbot) :=
        fun T e => on_mem (handle_intrinsic memM_interp e).

    but there the lambda comes out *without* the [<typename _T2>] header and
    with an explicit return type naming an unbound [T2]:

      [](memM<T2> _x0) -> Monads::stateT<State, std::shared_ptr, T2> { ... }

    I could not reduce that monomorphic variant -- four attempts, including a
    recursive [Fixpoint] natural transformation defined in a separate module,
    all produced the templated-lambda form above instead. This test covers the
    templated-lambda half only. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree Basics.Basics.
Import ITree.Basics.Basics.Monads.

Variant AE : Type -> Type := A0 : AE nat.
Variant FailE : Type -> Type := Throw : unit -> FailE void.

Definition st := nat.

Module M.
  Section S.
    Context {E} `{FailE -< E}.

    Definition base : AE ~> stateT st (itree E) :=
      fun _ e => match e with A0 => fun s => Ret (s, s) end.

    (* Takes the handler as a higher-order argument, so [base] is
       eta-expanded into a generic lambda at the call site. *)
    Definition run (h : AE ~> stateT st (itree E)) : AE ~> stateT st (itree E) :=
      fun T e s => h T e s.

    Definition fused : AE ~> stateT st (itree E) :=
      fun T e => run base T e.
  End S.

  Definition use (n : nat) : itree FailE (nat * nat) := fused nat A0 n.
End M.
Crane Extraction "eta_handler_event_as_template" M.
