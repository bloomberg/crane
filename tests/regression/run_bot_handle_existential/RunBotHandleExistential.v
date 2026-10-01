(** Crane bug (vanilla ITree): in a cofixpoint walking an itree, the call to
    an event handler whose result index is the [VisF]'s existential answer
    type is instantiated at the walker's *own* type variable.

    Observed (86aac86af), inside a [Context {Pa : Params}] section:
      template <Params _tcI0, typename T1>
      static Sum<Run_error, T1> handle_bot(const Sum1<outE<typename _tcI0::ptr>, FailE, T1> &e) {
        ... return Sum<Run_error, T1>::inr(std::monostate{}); ...    // [Out _ => inr tt], T := unit
      ...
      // in run_bot<_tcI0, T1>, T1 = the tree's result type X:
      auto &&_sv0 = handle_bot<_tcI0, T1>(x);
    [handle_bot]'s [T] is the [VisF]'s existential (erased, [std::any]),
    not [run_bot]'s [X].  Instantiated at [X := nat]:
      error: no viable conversion from 'std::monostate' to 'Nat'
    With closed families (no Params section) the same file compiles and
    runs.

    Reduced from Vellvm, [Semantics/Run.v] [handle_bot] / [run_bot]: the
    remaining [no viable conversion from 'std::monostate' to
    'std::pair<std::pair<State<...>, ...>>'] (Vellvm's [X] is [Res dvalue]).
    The vanilla counterpart of handler_loop_call_drops_result_targ (which
    uses ITreeReified). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.
Import ITreeNotations.

Module RunBotHandleExistential.
  Class Params : Type := { ptr : Type ; zero : ptr }.
  Variant run_error : Type := Failed.

  Section Run.
  Context {Pa : Params}.
  Variant outE : Type -> Type := Out : ptr -> outE unit.
  Variant failE : Type -> Type := Fail : failE void.
  Definition BotE := outE +' failE.

  (* Vellvm's Run.handle_bot: answer each event, dependently on its index. *)
  Definition handle_bot {T} (e : BotE T) : run_error + T :=
    match e with
    | inl1 o => match o in outE T return run_error + T with Out _ => inr tt end
    | inr1 f => match f in failE T return run_error + T with Fail => inl Failed end
    end.

  (* Vellvm's Run.run_bot: walk the tree to one with no events. *)
  CoFixpoint run_bot {X} (t : itree BotE X) : itree void1 (run_error + X) :=
    match observe t with
    | RetF x => Ret (inr x)
    | TauF t' => Tau (run_bot t')
    | VisF e k =>
        match handle_bot e with
        | inl err => Ret (inl err)
        | inr a => Tau (run_bot (k a))
        end
    end.

  Definition prog : itree BotE nat := Vis (inl1 (Out zero)) (fun _ => Ret 3).
  End Run.

  #[global] Instance natParams : Params := { ptr := nat ; zero := 0 }.

  Fixpoint run (fuel : nat) (t : itree void1 (run_error + nat)) : option nat :=
    match fuel with
    | O => None
    | S f => match observe t with
             | RetF (inr n) => Some n
             | RetF (inl _) => None
             | TauF t' => run f t'
             | VisF e _ => match e with end
             end
    end.
  Definition is_three : bool := match run 100 (run_bot prog) with Some n => Nat.eqb n 3 | None => false end.
End RunBotHandleExistential.

Crane Extraction "run_bot_handle_existential" RunBotHandleExistential.
