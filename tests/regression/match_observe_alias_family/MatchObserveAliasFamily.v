(** Crane bug: matching on [observe t] for [t : itree AllE R], where [AllE]
    is a family alias over a section variable, writes the scrutinee's
    alternatives with the family as [std::any].

    Observed (edb2edd97), in [run]:
      auto &&_sv0 = t.observe();   // ItreeF<Sum1<aE<Nat>, BE, std::any>, Nat, ...>
      if (std::holds_alternative<typename ItreeF<std::any, Nat, Itree<std::any, Nat>>::RetF>(_sv0.v()))
    The alternative types must be [ItreeF<Sum1<aE<Nat>, BE, std::any>, ...>::RetF]
    (the parameter [t] is spelled correctly).  Diagnostic, from libc++:
      error: static assertion failed due to requirement 'value != __not_found':
             type not found in type list
    With a closed local family ([Variant noE]) the same [run] compiles
    (itree_interp, itree_mrec).

    Reduced from Vellvm: the same static_assert appears twice in the
    interpretation stack on edb2edd97 ([Run.run_bot] and friends match on
    [observe] at [MCFGEbot] / [CFGEbot]). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.
From ExtLib Require Import Structures.Monad.
Import ITreeNotations.
Import MonadNotation.
Local Open Scope monad_scope.

Module MatchObserveAliasFamily.
  Section WithParam.
    Context {P : Type}.
    Variant aE : Type -> Type := A : P -> aE nat.
    Variant bE : Type -> Type := B : bE nat.
    Definition AllE := aE +' bE.
    Definition top := itree AllE.

  End WithParam.

  Variant noE : Type -> Type := .
  Fixpoint run (fuel : nat) (t : itree (@AllE nat) nat) : option nat :=
    match fuel with
    | O => None
    | S f => match observe t with
             | RetF r => Some r
             | TauF t' => run f t'
             | VisF _ _ => None
             end
    end.
  Definition is_three : bool := match run 100 (Ret 3 : itree (@AllE nat) nat) with Some n => Nat.eqb n 3 | None => false end.
End MatchObserveAliasFamily.

Crane Extraction "match_observe_alias_family" MatchObserveAliasFamily.
