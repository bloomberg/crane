(** Crane bug(s): ITree's [interp] with a handler into another itree does
    not compile.  An acceptance test for the feature (Vellvm's whole
    interpretation stack is [interp] of handlers): two [Get]s answered with 2
    each must give 4.

    Layers seen on 0b2cfbbd5:
    1. ITree's definitional instance
         Instance MonadIter_itree {E} : MonadIter (itree E) := fun _ _ => ITree.iter.
       is emitted with [E] higher-kinded,
         template <template <typename> class T1, typename F0>
         Itree<T1<std::any>, std::any> MonadIter_itree(F0 &&x0_, std::any x1_)
       and called as [MonadIter_itree<noE>(...)]:
         error: no matching function for call to 'MonadIter_itree'
         note: candidate template ignored: invalid explicitly-specified
               argument for template parameter 'T1'
       (0b2cfbbd5 fixed record-style instances over a family; this one is a
       function-valued instance.  A self-contained definitional instance over
       a local [box E] did *not* reproduce the higher-kinded [T1], so the
       library's own shape is used here.)
    2. [trigger] in [prog] goes through [subevent], whose [ReSum] dictionary
       is built at [std::any] ("no known conversion from 'ReSum<[...],
       std::any>' to 'ReSum<[...], IFun<std::any, std::any>>'"); see
       itree_trigger_subevent.

    Reduced from Vellvm's interpretation stack
    ([Semantics/InterpretationStack.v], [interp_mcfg*]). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.
Import ITreeNotations.
Local Open Scope itree_scope.

Module ItreeInterp.
  Variant getE : Type -> Type := Get : getE nat.
  Variant noE : Type -> Type := .

  Definition prog : itree getE nat := x <- trigger Get ;; y <- trigger Get ;; Ret (x + y).

  Definition h : getE ~> itree noE := fun _ e => match e with Get => Ret 2 end.

  Definition run_it : itree noE nat := interp h prog.

  Fixpoint run (fuel : nat) (t : itree noE nat) : option nat :=
    match fuel with
    | O => None
    | S f => match observe t with
             | RetF r => Some r
             | TauF t' => run f t'
             | VisF e _ => match e with end
             end
    end.
  Definition is_four : bool := match run 100 run_it with Some n => Nat.eqb n 4 | None => false end.
End ItreeInterp.

Crane Extraction "itree_interp" ItreeInterp.
