(** Events of a nested sum as shared variants, injected through the erased
    [ReSum] instances and dispatched by a [case_] of handlers: each event is
    boxed into [crane::obj] on the way into the erased instance and read back
    at its own type, or at the all-[crane::obj] instantiation the erased
    [case_] reads it at, on the way out. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.
Import ITreeNotations.
Local Open Scope itree_scope.

Module SharedEventSubevent.
  Variant aE : Type -> Type := GetA : aE nat.
  Variant bE : Type -> Type := GetB : nat -> bE nat.
  Variant cE : Type -> Type := GetC : nat -> cE bool.
  Definition E := aE +' bE +' cE.

  Definition prog : itree E nat :=
    a <- (trigger GetA : itree E nat) ;;
    b <- (trigger (GetB a) : itree E nat) ;;
    c <- (trigger (GetC b) : itree E bool) ;;
    Ret (if c then a + b else 0).

  Definition h_a : aE ~> itree void1 := fun _ e => match e with GetA => Ret 3 end.
  Definition h_b (k : nat) : bE ~> itree void1 := fun _ e => match e with GetB n => Ret (n * k) end.
  Definition h_c (k : nat) : cE ~> itree void1 := fun _ e => match e with GetC n => Ret (Nat.eqb n k) end.

  Definition run : itree void1 nat := interp (case_ h_a (case_ (h_b 2) (h_c 6))) prog.

  (** [run] with at most [n] silent steps taken. *)
  Fixpoint burn (n : nat) (t : itree void1 nat) : option nat :=
    match n with
    | O => None
    | S m =>
      match observe t with
      | RetF r => Some r
      | TauF t' => burn m t'
      | VisF e _ => match e with end
      end
    end.

  Definition result : option nat := burn 100 run.
  Definition ok : bool := match result with Some n => Nat.eqb n 9 | None => false end.
End SharedEventSubevent.

Set Crane SharedVariant.
Crane Extraction "shared_event_subevent" SharedEventSubevent.
