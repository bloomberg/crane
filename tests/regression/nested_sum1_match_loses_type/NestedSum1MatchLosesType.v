(** A match three [inr1]s deep into a sum of event families loses the
    scrutinee's type.

    The first two levels are taken apart at the sum's own type; from the
    third on, the payload is treated as a box --
    [std::any_cast<Sum1<std::any, std::any, std::any>>(a00)] -- and the
    binder it yields is a [std::any] the next level calls [.v()] on:

      error: no member named 'v' in 'std::any'

    The runtime [Sum1] types both its payloads, so nothing is boxed; the
    match lost the type after two levels.

    Reported by the Vellvm-side session at install #22, in [exc_of_event]
    (Denotation.v:834), nine [inr1]s deep into [CFGEtop]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.

Class Params := { ptr : Type ; nullp : ptr }.

Section S.
  Context {Pa : Params}.

  Inductive dvalue : Type := DP : ptr -> dvalue | DU : dvalue.

  Variant AE : Type -> Type := A0 : AE nat.
  Variant BE : Type -> Type := B0 : BE nat.
  Variant CE : Type -> Type := C0 : CE nat.
  Variant FailE : Type -> Type := Fail : dvalue -> FailE unit.
  Definition CFGEtop := AE +' BE +' CE +' FailE.

  Definition exc_of_event {X} (e : CFGEtop X) : option dvalue :=
    match e with
    | inr1 (inr1 (inr1 (Fail d))) => Some d
    | _ => None
    end.
End S.

#[global] Instance natParams : Params := {| ptr := nat ; nullp := 0 |}.

Module NestedSum1MatchLosesType.
  Definition run : option (@dvalue natParams) :=
    @exc_of_event natParams unit (inr1 (inr1 (inr1 (Fail DU)))).
End NestedSum1MatchLosesType.
Crane Extraction "nested_sum1_match_loses_type" NestedSum1MatchLosesType.
