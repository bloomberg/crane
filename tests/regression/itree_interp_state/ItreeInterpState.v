(** Crane bug (runtime): ITree's [interp_state] is extracted as a stub that
    throws.

    ITree/Events/State.v:
      Definition interp_state {E M S} {FM : Functor M} {MM : Monad M}
                 {IM : MonadIter M} (h : E ~> stateT S M) :
        itree E ~> stateT S M := interp h.
    Observed (post-a5d6c442b HEAD):
      template <Monad _tcI0, Functor _tcI1, typename T1, typename T3, typename T4, typename F1>
      Monads::template stateT<T3, _tcI0::template m, T4>
      State::interp_state(std::type_identity_t<MonadIter<_tcI0::template m>>, F1 &&, Itree<T1, T4>) {
        return [](const T3 &) -> typename _tcI0::template m<std::pair<T3, T4>> {
          throw std::logic_error("untranslatable curried proof term");
        };
      }
    It compiles, and throws when run:
      libc++abi: terminating due to uncaught exception of type
      std::logic_error: untranslatable curried proof term
    [interp h] here is [interp] at the monad [stateT S M], whose
    Monad/MonadIter dictionaries are built from [M]'s (ExtLib-style
    [Monad_stateT]); the body is a partial application returning a
    function of the state.

    Reduced from Vellvm: the compiled interpreter (the first time the
    vanilla artifact compiled with zero errors) gets past startup and dies
    here, in [InterpretationStack.interp_mcfg] = [interp_state
    interp_vellvm_h (interp_intrinsics t) s]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree Events.State.
From ExtLib Require Import Structures.Monad Data.Monads.StateMonad.
Import ITreeNotations.
Local Open Scope itree_scope.

Module ItreeInterpState.
  Variant getE : Type -> Type := Get : getE nat.
  Variant noE : Type -> Type := .

  Definition prog : itree getE nat := x <- trigger Get ;; y <- trigger Get ;; Ret (x + y).

  (* Vellvm's InterpretationStack.interp_mcfg:
     [interp_state interp_vellvm_h (interp_intrinsics t) s]. *)
  Definition h : getE ~> Monads.stateT nat (itree noE) :=
    fun _ e s => match e with Get => Ret (S s, s) end.

  Definition out : itree noE (nat * nat) := interp_state h prog 1.

  Fixpoint run (fuel : nat) (t : itree noE (nat * nat)) : option (nat * nat) :=
    match fuel with
    | O => None
    | S f => match observe t with
             | RetF r => Some r
             | TauF t' => run f t'
             | VisF e _ => match e with end
             end
    end.
  (* state 1 -> Get returns 1 (state 2) -> Get returns 2 (state 3): result 3 *)
  Definition is_three : bool := match run 100 out with Some (_, n) => Nat.eqb n 3 | None => false end.
End ItreeInterpState.

Crane Extraction "itree_interp_state" ItreeInterpState.
