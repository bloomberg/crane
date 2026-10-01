(** A call inside a tree's handler loop names none of its callee's template
    arguments, the class instance included.

    [exc_of_event] is declared [template <typename _tcI0, typename T1 = void>]
    -- the [Params] instance, then the event index [X], which nothing
    deduces.  Inside [run_exc]'s [VisF] branch it is called as

      auto _cs1 = exc_of_event(e);

      error: no matching function for call to 'exc_of_event'

    and [_tcI0] can only be named.  It takes the event type to be a sum of
    families behind a [Definition] ([CFGEtop := OtherE +' FailE]); with a
    single family the call is [exc_of_event<_tcI0, T1>(e)].

    Reproduces the Vellvm-side session's [exc_of_event] (Denotation.v:832),
    called from [run_exc]; [handle_bot] is the same shape. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.

Class Params := { ptr : Type ; nullp : ptr }.

Module Denot.
Section S.
  Context {Pa : Params}.

  Inductive dvalue : Type := DP : ptr -> dvalue | DU : dvalue.
  Definition exc : Type := dvalue.

  Variant FailE : Type -> Type := Fail : dvalue -> FailE unit.
  Variant OtherE : Type -> Type := Other : nat -> OtherE nat.
  Definition CFGEtop := OtherE +' FailE.
  Definition CFGtop := itree CFGEtop.

  Definition exc_of_event {X} (e : CFGEtop X) : option exc :=
    match e with
    | inr1 (Fail d) => Some d
    | _ => None
    end.

  Definition run_exc {A : Type} (t : CFGtop A) : CFGtop (exc + A) :=
    ITree.iter (fun u => match observe u with
      | RetF a => Ret (inr (inr a))
      | TauF u' => Ret (inl u')
      | VisF e k => match exc_of_event e with
                    | Some x => Ret (inr (inl x))
                    | None => Vis e (fun y => Ret (inl (k y)))
                    end
      end) t.
End S.
End Denot.

#[global] Instance natParams : Params := {| ptr := nat ; nullp := 0 |}.

Module HandlerLoopCallDropsInstance.
  Definition run : itree (@Denot.CFGEtop natParams) (@Denot.exc natParams + nat) :=
    @Denot.run_exc natParams nat (Ret 3).
End HandlerLoopCallDropsInstance.
Crane Extraction "handler_loop_call_drops_instance" HandlerLoopCallDropsInstance.
