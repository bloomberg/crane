(** Crane bug: a coinductive record parameterised by a type family
    ([E : Type -> Type]) is emitted with no template parameters at all.

    This is the shape of the ITree library's own [itree]:
    [CoInductive itree (E : Type -> Type) (R : Type) := go { _observe : itreeF E R (itree E R) }].
    Vellvm is now extracted with vanilla Crane (no [Monads.ITree*] mapping), so
    the ITree library is extracted from source, and every ITree program hits
    this first.  Even a one-definition [ITree.iter] countdown over [void1]
    fails to compile.

    Observed ([tree] below):
      struct tree {
        struct go { std::shared_ptr<treeF<T1, std::any, tree>> observe; };
        ...
      template <typename T1, typename T2> treeF<T1, T2, tree> observe() const
    - [struct tree] has no [template <template <typename> class E, typename R>],
      so [T1] is unbound inside it;
    - diagnostics:
        error: use of undeclared identifier 'T1'
        error: indirection requires pointer operand ('int' invalid)
        error: template argument for template template parameter must be a
               class template or type alias template

    Control, not in this file: the same test with [E : Type] instead of
    [E : Type -> Type] (and [VisF (e : E) (k : nat -> T)]) extracts to
    [template <typename E, typename R> struct tree] and compiles and runs.
    So the parameters are dropped only when one of them is higher-kinded.

    Reduced from Vellvm, src/crane/Extract.v with Mapping.Std only; the
    first ITree use in the artifact is [ITree.iter] via [Semantics/Run.v]
    [run]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module CoindFamilyParam.
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

  Variant voidE : Type -> Type := .

  CoFixpoint count (n acc : nat) : tree voidE nat :=
    match n with
    | O => go (RetF acc)
    | S n' => go (TauF (count n' (S acc)))
    end.

  Fixpoint run (fuel : nat) (t : tree voidE nat) : option nat :=
    match fuel with
    | O => None
    | S f => match observe t with
             | RetF r => Some r
             | TauF t' => run f t'
             | VisF e _ => match e with end
             end
    end.

  Definition result : option nat := run 100 (count 10 0).
  Definition is_ten : bool :=
    match result with Some n => Nat.eqb n 10 | None => false end.
End CoindFamilyParam.

Crane Extraction "coind_family_param" CoindFamilyParam.
