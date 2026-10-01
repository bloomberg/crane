(** Crane bug: a match on a family sum several [inr1]s deep still switches
    to [std::any_cast<Sum1<std::any, std::any, std::any>>] partway down
    (8655b62ec fixed the three-deep case, nested_sum1_match_loses_type).

    Observed (bac0be39f), matching [inr1 (inr1 (inr1 (inr1 (inl1 (E5 n)))))]
    over [e1 +' e2 +' e3 +' e4 +' e5 +' e6]:
      auto &&_sv1 = std::any_cast<Sum1<std::any, std::any, std::any>>(a00);
      ... std::get<typename Sum1<std::any, std::any, std::any>::Inr1>(_sv1.v()) ...
      ... a01.v() ...       // a01 : std::any
    Diagnostic:
      error: no member named 'v' in 'std::any'

    Reduced from Vellvm, [Semantics/Denotation.v:834] [exc_of_event]
    (nine levels: [inr1 (inr1 ... (inl1 (LLVMExc x))))]) over the
    twelve-family [CFGEtop]: one of Vellvm's twelve remaining errors on
    bac0be39f. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.

Module DeepSum1Match.
  Variant e1 : Type -> Type := E1 : e1 nat.
  Variant e2 : Type -> Type := E2 : e2 nat.
  Variant e3 : Type -> Type := E3 : e3 nat.
  Variant e4 : Type -> Type := E4 : e4 nat.
  Variant e5 : Type -> Type := E5 : nat -> e5 unit.
  Variant e6 : Type -> Type := E6 : e6 nat.

  Definition AllE := e1 +' e2 +' e3 +' e4 +' e5 +' e6.

  (* Vellvm's exc_of_event: a match many [inr1]s deep, generic in X. *)
  Definition get5 {X : Type} (e : AllE X) : option nat :=
    match e with
    | inr1 (inr1 (inr1 (inr1 (inl1 (E5 n))))) => Some n
    | _ => None
    end.

  Definition is_three : bool :=
    match get5 (inr1 (inr1 (inr1 (inr1 (inl1 (E5 3))))) : AllE unit) with
    | Some n => Nat.eqb n 3 | None => false end.
End DeepSum1Match.

Crane Extraction "deep_sum1_match" DeepSum1Match.
