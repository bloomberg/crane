(** Crane bug: a reified [Vis] event matched where it is bound has no type.

    The [itreeF] custom match binds the event as a [crane_event] -- a thunk
    plus a [template <typename E> operator E()] that recovers the real event
    type lazily.  That works wherever the event is {e used} at a type: handed
    to a function whose parameter says what it is, the conversion fires and
    the right thing arrives.

    Matching on the event in the branch that binds it is the case with no such
    site.  The match is compiled against the event inductive, so it reaches for
    the variant accessor, and a [crane_event] has none:

      error: no member named 'v' in 'crane_event'

    Seen 3 times in Vellvm, all on one binder in [Recursion.interp_mrec].
    The sibling reduction [event_param_dropped] stays green precisely because
    it passes the event to [exc_of_event], whose parameter supplies the type.

    Expected: extracted C++ compiles.
    Actual:   error: no member named 'v' in 'crane_event' *)

From Crane Require Import Mapping.Std.
From Crane Require Import Monads.ITreeReified.
From Crane Require Extraction.
From ITree Require Import ITree.

Module EventMatchUntyped.

  Variant IOE : Type -> Type :=
    | Rd : IOE nat
    | Wr : nat -> IOE nat.

  (** The event is matched in the very branch that binds it, so nothing
      downstream says what type it has. *)
  Definition weight (t : itree IOE nat) : nat :=
    match observe t with
    | RetF r => r
    | TauF _ => 0
    | @VisF _ _ _ X e k =>
        match e in IOE T return nat with
        | Rd => 1
        | Wr n => n
        end
    end.

End EventMatchUntyped.

Crane Extraction "event_match_untyped" EventMatchUntyped.
