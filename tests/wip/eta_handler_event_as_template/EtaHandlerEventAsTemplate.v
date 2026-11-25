(** A natural transformation passed as a higher-order argument is
    eta-expanded at the call site ([run base]).  Vellvm has the same
    construct via src/rocq/Semantics/InterpretationStack.v:79
    (fused_intrinsic).

    The face this was filed for ([const AE<_T2> &] for an enum [AE]) is
    gone: the eta lambda now takes [const AE &].  Diagnosed 2026-11-24, three
    layers remain:

    1. [base<T1>(a0)]: [base]'s head is [<T1, T2>], [T2] its index, which
       only its return type names.  The eta lambda writes the type arguments
       the use instantiates ([E] only); the index is bound by the lambda the
       Rocq term is, not by the use, and nothing writes it.  The erased
       instantiation ([base<T1, crane::obj>]) is what the slot ([run]'s
       [crane::fn<stateT<st, itree_tc, crane::obj>(AE)>]) reads; a method
       named the same way is now written so
       ([Cpp_passes.Erasure.method_type_args]), the free-function value path
       ([Expr]'s global case, [Calls.written_at_variables]) is not.
    2. [base]'s body: [fun s => Ret (s, s)] at [stateT st (itree E) nat] is
       coerced as a whole lambda to [stateT st (itree E) T]; the lambda
       returns [ITree<pair<Nat, Nat>>] and does not convert to
       [crane::fn<ITree<pair<Nat, T2>>(Nat)>].  The coercion would have to
       be pushed into the lambda's body ([Coerce] of an arrow type around a
       [Lambda] whose domains agree), before position planning, which keys
       every coercion by its occurrence.
    3. [run]'s body: [crane::apply2(h, e, s)] for the rank-2 parameter [h]
       returns [ITree<pair<Nat, crane::obj>>] where [T2] is promised: the
       consumer-side recovery described in handler_lambda_targ_undeclared. *)

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
