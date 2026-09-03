From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.

Module HktCurriedPureArity.

(** A curried two-argument lambda passed to [pure] is typed as an uncurried
    [std::function], so the partially-applied [ap] no longer matches:

      pure<ApOpt, std::function<Nat(Nat, Nat)>>(
          [](const auto &x, const auto &) { return x; })

    should be [std::function<std::function<Nat(Nat)>(Nat)>].

    error: no matching function for call to 'ap' *)

Class Apply (F : Type -> Type) := {
  pure : forall A : Type, A -> F A ;
  ap : forall A B : Type, F (A -> B) -> F A -> F B
}.
Arguments pure {F _ A} _.
Arguments ap {F _ A B} _ _.

Instance ApOpt : Apply option := {
  pure := fun A x => Some x ;
  ap := fun A B f o =>
    match f with
    | None => None
    | Some g => match o with None => None | Some x => Some (g x) end
    end
}.

Definition run (a b : option nat) : option nat :=
  ap (ap (pure (fun x y : nat => x)) a) b.

End HktCurriedPureArity.

Crane Extraction "hkt_curried_pure_arity" HktCurriedPureArity.run.
