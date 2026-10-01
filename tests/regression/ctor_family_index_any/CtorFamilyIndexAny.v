(** Crane bug: a constructor of a family-indexed type whose family index is
    fixed only by context is written with the index as [std::any].

    Observed, in [ret {E R} (r : R) : tree E R := go (RetF r)]:
      return tree<T1, T2>::go(treeF<std::any, T2, tree<std::any, T2>>::retf(r));
    The inner [treeF] should be [treeF<T1, T2, tree<T1, T2>>].  Converting
    [treeF<std::any, ...>] to [treeF<noE, ...>] instantiates the converting
    constructor's Vis branch, [VisF{E(x), ...}] with [x : std::any].
    Diagnostic:
      error: no matching conversion for functional-style cast from
             'const std::any' to 'CtorFamilyIndexAny::noE'
    With a family that happens to be spelled [std::any] (e.g. [void1]) it
    compiles, which is why the tiny ITree probes did not show it; Vellvm's
    event families are real structs.

    Reduced from Vellvm's vanilla-ITree extraction: ITree's [Ret] /
    [ITree.iter] body ([Ret (inr acc)]) come out as
    [ItreeF<std::any, ...>::retf(...)] inside [Itree<E, ...>::go]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module CtorFamilyIndexAny.
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

  (* A constructor whose family index E is fixed only by context. *)
  Definition ret {E : Type -> Type} {R : Type} (r : R) : tree E R := go (RetF r).

  Definition t0 : tree noE nat := go (TauF (go (TauF (go (RetF 2))))).
  Definition t1 : tree noE nat := ret 3.
  Definition is_three : bool :=
    match run 10 t1 with Some n => Nat.eqb n 3 | None => false end.
End CtorFamilyIndexAny.

Crane Extraction "ctor_family_index_any" CtorFamilyIndexAny.
