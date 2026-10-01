(** A match on a call's result spells the result at the wrong type
    variable.

    [handle_bot] returns [nat + X], where [X] is the event's index.  Called
    from [run_exc]'s [VisF] branch, [X] is [VisF]'s existential answer type,
    which C++ has erased -- the event is cast to [Sum1<..., std::any>] and
    [handle_bot<_tcI0>(e)] deduces [X] as [std::any].  The match on the
    result, though, spells it [Sum<Nat, T1>], with [T1] being [run_exc]'s own
    result type, and asks the variant for an alternative it does not have:

      error: static assertion failed due to requirement
             'value != __not_found': type not found in type list

    Writing [X] out at the call would not help: the argument is the erased
    event, and would not convert.  The existential has to be spelled erased
    where the match reads it.

    Where [T1] comes from: extraction writes the call's type argument for
    [X] as [Tvar 2] -- [db_from_rel_context] numbers every type-sorted
    binder in scope, and [VisF]'s existential is one, after [A] -- but by
    translation the call carries [Tvar 1], [A]'s number, so the two were
    merged somewhere in between.  The match's scrutinee annotation is
    [sum nat ?]; its hole is filled from the call's instantiated codomain
    ([infer_ml_body_type]), and that is where [T1] enters.

    Reported by the Vellvm-side session at install #22, in [run_bot] /
    [handle_bot]. *)

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

  Definition handle_bot {X} (e : CFGEtop X) : nat + X :=
    match e with
    | inl1 o => match o in OtherE Y return nat + Y with Other n => inr n end
    | inr1 _ => inl 0
    end.

  Definition run_exc {A : Type} (t : CFGtop A) : CFGtop (exc + A) :=
    ITree.iter (fun u => match observe u with
      | RetF a => Ret (inr (inr a))
      | TauF u' => Ret (inl u')
      | VisF e k => match handle_bot e with
                    | inl n => Ret (inr (inl (DU)))
                    | inr y => Ret (inl (k y))
                    end
      end) t.
End S.
End Denot.

#[global] Instance natParams : Params := {| ptr := nat ; nullp := 0 |}.

Module HandlerLoopCallDropsResultTarg.
  Definition run : itree (@Denot.CFGEtop natParams) (@Denot.exc natParams + nat) :=
    @Denot.run_exc natParams nat (Ret 3).
End HandlerLoopCallDropsResultTarg.
Crane Extraction "handler_loop_call_drops_result_targ" HandlerLoopCallDropsResultTarg.
