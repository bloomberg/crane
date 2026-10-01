(** Crane bug: the self-call of a [cofix] whose result index occurs only in
    its return type is emitted without template arguments, so C++ cannot
    deduce them.

    This is [ITree.subst]'s shape ([cofix _subst (u : itree E T) : itree E U]),
    which every [ITree.bind] and [ITree.iter] goes through.  Here the Vis
    case is routed through a parameter so that the only defect exercised is
    the self-call (see vis_cont_type for the Vis continuation).

    Observed:
      template <typename T1, typename T2, typename T3, ...>
      static tree<T1, T3> subst(F0 &&k, F1 &&kv, tree<T1, T2> u) {
        ... treeF<T1, T3, tree<T1, T3>>::tauf(subst(k, kv, t2)) ...
    Diagnostic:
      error: no matching function for call to 'subst'
    Hand-writing [subst<T1, T2, T3>(...)] at the self-call fixes it (checked
    on the extracted ITree library itself, where a countdown via ITree.iter
    then runs correctly).

    Reduced from Vellvm's vanilla-ITree extraction (src/crane/Extract.v with
    Mapping.Std only), via the ITree library's [ITree.subst]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module CofixSelfCallTargs.
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

  (* ITree.subst's shape with the Vis case not rebuilding a Vis: the
     result index U occurs only in the return type, so the self-call
     cannot deduce it. *)
  Definition subst {E : Type -> Type} {T U : Type} (k : T -> tree E U)
    (kv : tree E T -> tree E U) : tree E T -> tree E U :=
    cofix _subst (u : tree E T) : tree E U :=
      match observe u with
      | RetF r => k r
      | TauF t => go (TauF (_subst t))
      | VisF _ _ => kv u
      end.

  Definition t0 : tree noE nat := go (TauF (go (TauF (go (RetF 2))))).
  Definition t1 : tree noE nat := subst (fun n => go (RetF (S n))) (fun u => u) t0.
  Definition is_three : bool :=
    match run 10 t1 with Some n => Nat.eqb n 3 | None => false end.
End CofixSelfCallTargs.

Crane Extraction "cofix_self_call_targs" CofixSelfCallTargs.
