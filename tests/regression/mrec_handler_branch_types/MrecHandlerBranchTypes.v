(** Crane bug: mrec's handler ([fun T call => match call with ...] of type
    [callE ~> itree (callE +' E)]) is emitted as a lambda with no explicit
    return type whose branches return different [Itree] instantiations.

    Observed (bac0be39f):
      [](const callE &call) { ...
          if (...) return Itree<Sum1<callE, OtherE<T1, std::any>, std::any>, std::any>::go(...);
          else     return Functor0::template fmap<Functor_itree<Sum1<callE, OtherE<T1, std::any>, std::any>>,
                                                  Nat, Sum<Nat, Nat>>(..., ext_call<T1>(a0));   // Itree<..., Sum<Nat, Nat>>
    The handler's index [T] is erased (it is the [forall T] of [~>]), so
    the lambda's result should be the erased-index tree in every branch
    (or be written with an explicit return type the branches convert to).
    Diagnostic:
      error: return type 'Itree<[...], Sum<Nat, Nat>>' must match previous
             return type 'Itree<[...], std::any>' when lambda expression has
             unspecified explicit return type

    Reduced from Vellvm, [Semantics/Denotation.v] [denote_mcfg]:
      @mrec CallE (ExternalCallE +' _) (fun T call => match call with
        | Call dt fv args => match lookup_defn fv fundefs with
            | Some f_den => f_den args
            | None => inr <$> external_call dt fv args end end) _ (Call ...)
    where Vellvm's variant of the same error is
      return type 'Itree<Sum1<std::any, std::any, [...]>, [...]>' must match
      previous return type 'Itree<Sum1<CallE<...>, Sum1<ExternalCallE<...>, ...
    (the [fmap] branch's instance is [Functor_itree<Sum1<std::any, std::any,
    std::any>>], i.e. the family also erased there).  One of Vellvm's twelve
    remaining errors. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.
From ExtLib Require Import Structures.Monad Structures.Functor.
Import ITreeNotations.
Import FunctorNotation.
Local Open Scope monad_scope.

Module MrecHandlerBranchTypes.
  Section WithParam.
    Context {P : Type}.
    Variant callE : Type -> Type := Call : nat -> callE (nat + nat).
    Variant extE : Type -> Type := Ext : P -> extE nat.
    Variant failE : Type -> Type := Fail : failE unit.
    Definition OtherE := extE +' failE.

    Definition ext_call (n : nat) : itree (callE +' OtherE) nat :=
      Ret (n + 1).

    (* Vellvm's Denotation.denote_mcfg: in mrec's handler, one branch is
       another tree, the other an ExtLib [fmap] ([inr <$> external_call ...]). *)
    Definition den (n : nat) : itree OtherE (nat + nat) :=
      @mrec callE OtherE
        (fun T call =>
           match call in callE T return itree (callE +' OtherE) T with
           | Call k => match k with
                       | O => Ret (inl 0)
                       | S _ => inr <$> ext_call k
                       end
           end) _ (Call n).
  End WithParam.

  Fixpoint run (fuel : nat) (t : itree (@OtherE nat) (nat + nat)) : option (nat + nat) :=
    match fuel with
    | O => None
    | S f => match observe t with
             | RetF r => Some r
             | TauF t' => run f t'
             | VisF _ _ => None
             end
    end.
  Definition is_three : bool :=
    match run 100 (@den nat 2) with Some (inr n) => Nat.eqb n 3 | _ => false end.
End MrecHandlerBranchTypes.

Crane Extraction "mrec_handler_branch_types" MrecHandlerBranchTypes.
