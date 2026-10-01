(* An event family that is a sum ([E +' F]) has no C++ spelling: [sum1] is
   extracted to the empty string, because the event is erased wherever it
   appears.  Two things followed from that, and both are fixed here.

   A call's explicit template arguments are all-or-nothing -- the positions are
   what give them their meaning, so one that cannot be written drops the rest.
   The event, though, is a phantom parameter, and a phantom position has a
   filler that is right whatever the argument was.  Without it, [raise]'s
   result type went unwritten too, and it appears only in the return position:

     error: no matching function for call to 'raise0'
     note: candidate template ignored: couldn't infer template argument 'T2'

   And an abbreviation for an unspellable type is not written either:

     template <typename x> using E2 = ;   error: expected a type

   In Vellvm this is 40 errors: [LLVMEvents::raise] 34 and [raiseUB] 6, from
   rocq/Semantics/LLVMEvents.v:176-193. *)
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
