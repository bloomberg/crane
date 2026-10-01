(** A custom constructor nested in another takes the outer one's field type
    as its own.

    In [run_exc], [Ret (inr (inr a)) : itree E (itree E A + (exc + A))]
    builds the inner [inr] at [exc + A], the outer [inr]'s field.  Giving a
    custom constructor's argument its field's type (rather than the
    constructor's i-th type argument) made the inner constructor come out one
    level too deep:

      Sum<ITree<T1>, Sum<Dvalue, T1>>::inr(Sum<Dvalue, Sum<Dvalue, T1>>::inr(a))

    and the same for [inl x].  It takes the [Params] section, and [exc] over
    a promoted type, to reproduce; a plain [nat + (bool + A)] comes out
    right.

    Reported by the Vellvm-side session at install #19, in [run_exc]
    (Semantics/Denotation.v:838), as a regression from 56ea1fc04. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.

Class Params := { ptr : Type ; nullp : ptr }.

Section S.
  Context {Pa : Params}.

  Inductive dvalue : Type := DP : ptr -> dvalue | DU : dvalue.
  Definition exc : Type := dvalue.

  Variant FailE : Type -> Type := Fail : FailE unit.
  Definition CFGtop := itree FailE.

  Definition exc_of_event {X} (e : FailE X) : option exc := None.

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

#[global] Instance natParams : Params := {| ptr := nat ; nullp := 0 |}.

Module NestedCustomCtorFieldType.
  Definition run : itree FailE (@exc natParams + nat) := @run_exc natParams nat (Ret 3).
End NestedCustomCtorFieldType.
Crane Extraction "nested_custom_ctor_field_type" NestedCustomCtorFieldType.
