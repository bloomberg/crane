(* When the event family at a call site is a *sum* ([E +' F]), the reified
   backend erases it to [void] -- and in doing so emits that erased event as
   the function's *first and only* explicit template argument, dropping the
   result type argument that follows it.  The callee needs both, and the
   result type appears only in the return position, so it cannot be deduced.

   Expected: [raise0<void, std::pair<Nat, Nat>>(Nat::o())]
   Actual:   [raise0<void>(Nat::o())]
     error: no matching function for call to 'raise0'
     note: candidate template ignored: couldn't infer template argument 'T2'

   Replacing [E2] with a single non-sum event ([FailE]) makes Crane emit both
   arguments correctly, so the sum is the trigger.

   In Vellvm this is 40 errors: [LLVMEvents::raise] 34 and [raiseUB] 6, from
   rocq/Semantics/LLVMEvents.v:176-193.  Declaration at vellvm_bench.h:14591
   is [template <typename T1, typename T2> ... LLVMEvents::raise(const String&)];
   every call site spells it [LLVMEvents::template raise<void>(msg)]. *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.
From Stdlib Require Import List.
Import ListNotations.

Variant FailE : Type -> Type := Throw : unit -> FailE void.

Definition cast' {E : Type -> Type} {A : Type} `{FailE -< E} (e : FailE void)
  : itree E A :=
  ITree.bind (trigger e) (fun v : void => match v with end).

Definition raise {E} {A} `{FailE -< E} (n : nat) : itree E A := cast' (Throw tt).

Definition E2 := (FailE +' FailE)%type.

Module SumEventDropsResultTarg.
  Definition use (l : list nat) : itree E2 (nat * nat) :=
    match l with
    | [] => raise 0
    | x :: _ => Ret (x, x)
    end.
End SumEventDropsResultTarg.

Crane Extraction "sum_event_drops_result_targ" SumEventDropsResultTarg.
