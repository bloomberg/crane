From Crane Require Import Mapping.Std.
From Crane Require Import Monads.ITreeReified.
From Crane Require Extraction.
From ITree Require Import ITree.
From Stdlib Require Import List.

Class Provenance := { prov : Set }.
Class Params := { PROV :: Provenance }.

Module Denotation.
Section S.
  Context {Pa : Params}.

  Definition exc := prov.

  Variant FailE : Type -> Type := Fail : exc -> FailE void.
  Variant TickE : Type -> Type := Tick : TickE prov.

  Definition E := TickE +' FailE.

  Definition exc_of_event {X} (e : E X) : option exc :=
    match e with
    | inr1 (Fail x) => Some x
    | _ => None
    end.

  Definition run_exc {A} (t : itree E A) : itree E (exc + A) :=
    ITree.iter
      (fun u =>
         match observe u with
         | RetF a => Ret (inr (inr a))
         | TauF u' => Ret (inl u')
         | @VisF _ _ _ X e k =>
             match exc_of_event e with
             | Some x => Ret (inr (inl x))
             | None => Vis e (fun y => Ret (inl (k y)))
             end
         end) t.

End S.
End Denotation.

Module EventParamDropped.
  Definition use `{Params} (t : itree Denotation.E prov) : itree Denotation.E (prov + prov) := Denotation.run_exc t.
End EventParamDropped.

Crane Extraction "event_param_dropped" EventParamDropped.
