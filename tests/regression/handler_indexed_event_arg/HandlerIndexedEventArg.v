(* An eta-expanded handler whose argument still carries the index.

   The sibling of handler_lambda_targ_undeclared, which reduces the case where
   the handler's argument is a bare enum: erasure takes the quantified index
   out of it, so nothing at the call deduces it. Here the argument is [memM T]
   -- a type constructor that survives extraction -- so the index is
   structurally present in the lambda's own parameter, and C++ deduces it.

   Eta-expansion invents that index and so has to bind it; before it did, the
   lambda's return type named a free T2 under a head declaring only T1. It now
   comes out as

     []<typename T2>(MemM<T2> _x0) -> Monads::template stateT<st, itree_tc, T2>

   with the index a template parameter of the lambda, deduced from the
   argument, and no consumer change needed.

   The typeclass context is load-bearing: it is what sends the handler down
   the eta-expansion path rather than the rank-2 one. Without it the same
   program takes the rank-2 path and emits a [decltype(auto)] lambda with a
   nonsense [std::invoke_result_t] filler -- that face is
   eta_handler_event_as_template, and is still open.

   This is the shape Vellvm's fused_intrinsic chain is made of: nine copies of
   the free-name error, which cleared with the binding fix. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.
From ExtLib Require Import Structures.Monads.
Import ITree.Basics.Basics.Monads.

Definition st := nat.

(* An indexed carrier for the handler's argument: unlike an enum event, this
   one still mentions its index after extraction. *)
Inductive memM (T : Type) : Type := | MemRet : T -> memM T.
Arguments MemRet {T} _.

(* The typeclass context is load-bearing: it is what sends the handler down
   the eta-expansion path rather than the rank-2 one, and it is what Vellvm's
   fused_intrinsic chain has (its lambdas are emitted under a [_tcI0]). *)
Class Params := { width : nat }.

Section S.
  Context {Pa : Params}.
  Context {E : Type -> Type}.

  Definition base : memM ~> stateT st (itree E) :=
    fun _ m => match m with
               | MemRet x => fun s => Ret (s + width, x)
               end.

  Definition run (h : memM ~> stateT st (itree E))
    : memM ~> stateT st (itree E) := fun T m => h T m.
End S.

Section T.
  Context {Pa : Params}.

  Definition fused : memM ~> stateT st (itree memM) :=
    fun T m => run base T m.
End T.

Module HandlerIndexedEventArg.
  Definition go `{Params} (n : nat) : itree memM (st * nat) :=
    fused _ (MemRet n) n.
End HandlerIndexedEventArg.

Crane Extraction "handler_indexed_event_arg" HandlerIndexedEventArg.
