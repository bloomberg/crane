(** Crane bug: rebuilding a [VisF] node with a continuation types the
    continuation as [X -> R] instead of [X -> tree E R].

    Observed, in [vmap]:
      treeF<T1, T3, tree<T1, T3>>::visf(x,
          std::function<T3(std::any)>([=](const std::any &x0) mutable -> T3 {
            return k(e0(x0)); }))
    The field is [std::function<T(std::any)>] with [T = tree<T1, T3>], so
    the lambda should return [tree<T1, T3>].  Diagnostic:
      error: no viable conversion from returned value of type
             'tree<noE, Nat>' to function return type 'Nat'
    Hand-writing [std::function<tree<T1, T3>(std::any)>] and the lambda's
    return type fixes it (checked on the extracted ITree library).

    Reduced from Vellvm's vanilla-ITree extraction, via [ITree.subst]'s
    [VisF e h => Vis e (fun x => _subst (h x))] branch. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module VisContType.
  Variant treeF (E : Type -> Type) (R : Type) (T : Type) : Type :=
  | RetF (r : R)
  | TauF (t : T)
  | VisF {X : Type} (e : E X) (k : X -> T).
  Arguments RetF {E R T}.
  Arguments TauF {E R T}.
  Arguments VisF {E R T X}.

  CoInductive tree (E : Type -> Type) (R : Type) : Type :=
    go { observe : treeF E R (tree E R) }.
  Arguments go {E R}.
  Arguments observe {E R}.

  Variant noE : Type -> Type := .

  Fixpoint run (fuel : nat) (t : tree noE nat) : option nat :=
    match fuel with
    | O => None
    | S f => match observe t with
             | RetF r => Some r
             | TauF t' => run f t'
             | VisF e _ => match e with end
             end
    end.

  (* Rebuilds a Vis with a continuation; no self-call, and no constructor
     whose family index is left to context. *)
  Definition vmap {E : Type -> Type} {T U : Type} (k : tree E T -> tree E U)
    (u : tree E T) : tree E U :=
    match observe u with
    | RetF _ => k u
    | TauF t => k t
    | VisF e h => go (VisF e (fun x => k (h x)))
    end.

  Definition t0 : tree noE nat := go (TauF (go (TauF (go (RetF 2))))).
  Definition t1 : tree noE nat := vmap (fun t => t) t0.
  Definition is_three : bool :=
    match run 10 t1 with Some n => Nat.eqb n 2 | None => false end.
End VisContType.

Crane Extraction "vis_cont_type" VisContType.
