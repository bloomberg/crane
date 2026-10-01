(** Crane bug: a stateful handler ([h : E ~> Monads.stateT S (itree F)],
    here [case_ h_get h_inc]) passed to [interp_state] is wrapped in a
    lambda over the *state* instead of being passed as the event handler.

    Observed (post-itree_interp_state HEAD):
      State::template interp_state<Monad_itree<noE>, Functor_itree<noE>, std::any, Nat, Nat>(
          [](auto &&_ec0, std::any _ec1) { return MonadIter_itree<noE>(_ec0, _ec1); },
          [](const Nat &) { return h; },            // should be (a callable for) h itself
          prog)(Nat::o());
    [interp] then calls [h(x)] with an event [x]:
      error: cannot deduce return type 'auto' from returned value of type
             '<overloaded function type>'
      error: no matching function for call to object of type '(lambda ...)'
    ([h] is a function template, hence "overloaded function type".)

    Reduced from Vellvm: the compiled-with-zero-errors artifact of the
    previous install stops compiling here once interp_state is real,
    [InterpretationStack.interp_mcfg] passing
      [](FusedS<...>) { return [](const auto &_x0) -> stateT<...> {
          return interp_vellvm_h<_tcI0>(crane_convert<MCFGEtop<...>>(_x0)); }; }
    for [interp_vellvm_h : MCFGEtop ~> stateT FusedS (itree MCFGEbot)]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree Events.State.
Import ITreeNotations.
Local Open Scope itree_scope.

Module InterpStateCaseHandler.
  Variant getE : Type -> Type := Get : getE nat.
  Variant incE : Type -> Type := Inc : incE unit.
  Variant noE : Type -> Type := .

  Definition prog : itree (getE +' incE) nat :=
    trigger Inc ;; x <- trigger Get ;; trigger Inc ;; y <- trigger Get ;; Ret (x + y).

  Definition h_get : getE ~> Monads.stateT nat (itree noE) :=
    fun _ e s => match e with Get => Ret (s, s) end.
  Definition h_inc : incE ~> Monads.stateT nat (itree noE) :=
    fun _ e s => match e with Inc => Ret (S s, tt) end.

  (* Vellvm's InterpretationStack.interp_vellvm_h: a case_ of per-family
     stateful handlers, passed unapplied to interp_state. *)
  Definition h : getE +' incE ~> Monads.stateT nat (itree noE) := case_ h_get h_inc.

  Definition out : itree noE (nat * nat) := interp_state h prog 0.

  Fixpoint run (fuel : nat) (t : itree noE (nat * nat)) : option (nat * nat) :=
    match fuel with
    | O => None
    | S f => match observe t with
             | RetF r => Some r
             | TauF t' => run f t'
             | VisF e _ => match e with end
             end
    end.
  (* 0 -Inc-> 1, Get = 1, -Inc-> 2, Get = 2: result 3 *)
  Definition is_three : bool := match run 200 out with Some (_, n) => Nat.eqb n 3 | None => false end.
End InterpStateCaseHandler.

Crane Extraction "interp_state_case_handler" InterpStateCaseHandler.
