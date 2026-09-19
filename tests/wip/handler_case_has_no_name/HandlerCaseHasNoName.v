(* The other two remaining nameless-callee sites, both from an [interp] whose
   handler is a [case_] of two [Handler]s.  Two distinct shapes come out of
   one definition:

   Expected: named callees for [case_] and for applying a [Handler] (a [~>]
             natural transformation) to an event.
   Actual:
       return <std::any, std::any>(                      // case_, no callee
       ...
       -> std::shared_ptr<ITree<std::any>> { return <void>()(_x0); }
                                                   ^ no callee, *empty*
                                                     template argument list,
                                                     then invoked on _x0
     error: expected expression
     error: expected '(' for function-style cast or type construction

   In Vellvm these are the last 2 of the 5 nameless-callee sites after
   1e85ca2d9: vellvm_bench.h:16251, inside [Intrinsics::interp_intrinsics] in
   the function passed to [Interp::template interp<Monad_itree<std::any>>],
   and :19406.  Source is rocq/Semantics/Handlers/Intrinsics.v:91-99:

       Definition E_trigger : Handler E Eff := fun _ e => trigger e.
       Definition F_trigger : Handler F Eff := fun _ e => trigger e.
       Definition interp_intrinsics_h := case_ E_trigger (case_ ... F_trigger).
       Definition interp_intrinsics := interp interp_intrinsics_h.

   [interp] and [Monad_itree] are both spelled since 1e85ca2d9; it is [case_]
   and the [Handler] application that still have nothing to name. *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.
From Stdlib Require Import List.
Import ListNotations.

Variant AE : Type -> Type := A0 : AE nat.
Variant BE : Type -> Type := B0 : BE nat.

Definition Eff := (AE +' BE)%type.

Definition e_trigger : Handler AE Eff := fun _ e => trigger e.
Definition b_trigger : Handler BE Eff := fun _ e => trigger e.

Definition h := case_ e_trigger b_trigger.

Module HandlerCaseHasNoName.
  Definition use (n : nat) : itree Eff nat := interp h (Ret n).
End HandlerCaseHasNoName.

Crane Extraction "handler_case_has_no_name" HandlerCaseHasNoName.
