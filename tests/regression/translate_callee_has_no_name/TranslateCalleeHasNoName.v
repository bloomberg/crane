(* [ITree.translate] has no spelling in the reified mode, so in callee position
   it leaves the template argument list with nothing in front of it -- the same
   shape [ITree.iter] had before 1e85ca2d9 (see the [iter_callee_has_no_name]
   regression test).  The handler argument additionally prints its parameter as
   the literal [axiom].

   Expected: in the reified mode [translate h t] should be the identity on [t].
             A Vis node stores its effect as a [std::function<std::any()>]
             thunk, so relabelling the event family changes nothing about the
             runtime representation -- [%a1], dropping the handler, the way
             [subevent => "%a0"] already works.  No helper needed.
   Actual:
       std::shared_ptr<ITree<T1>> w(const std::shared_ptr<ITree<T1>> &x) {
         return <AE, std::any, T1>([=](axiom) mutable { return sum1_inl(x0); }, x);
                ^ no callee              ^ parameter printed as [axiom]
       }
     error: expected expression
     error: expected '(' for function-style cast or type construction

   In Vellvm this is 3 of the 5 remaining nameless-callee sites:
   vellvm_bench.h:14615 is [LLVMEvents::withCall], whose source is exactly
   [Definition withCall : MCFGtop ~> CFGtop := translate inr1.]
   (rocq/Semantics/LLVMEvents.v:216); same shape at :16228 and :19324.
   The partially-applied [~>] form below is deliberate -- that is how Vellvm
   writes it. *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.
From Stdlib Require Import List.
Import ListNotations.

Variant AE : Type -> Type := A0 : AE nat.
Variant BE : Type -> Type := B0 : BE nat.

Definition w : itree AE ~> itree (AE +' BE) := translate inl1.

Module TranslateCalleeHasNoName.
  Definition use (n : nat) : itree (AE +' BE) nat := w _ (Ret n).
End TranslateCalleeHasNoName.

Crane Extraction "translate_callee_has_no_name" TranslateCalleeHasNoName.
