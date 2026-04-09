From Stdlib Require Import Nat.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITreeReified.
Require Crane.Extraction.

Set Crane Loopify.

Module IO_axioms.
  Axiom ioE : Type -> Type.
End IO_axioms.
Crane Extract Skip Module IO_axioms.
Export IO_axioms.

Module LoopifyItreeReified.

(** Consumer fixpoint: traverses an ITree with fuel. This is a regular
    fixpoint with recursion on fuel that processes reified ITrees. Should
    be loopified normally (nontail with _Enter/_Call frames). *)
Fixpoint count_taus (fuel : nat) (t : itree ioE nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
    match observe t with
    | RetF _ => 0
    | TauF t' => S (count_taus fuel' t')
    | VisF _ _ => 0
    end
  end.

(** HOF-pattern cofixpoint body: identity traversal on ITrees. Takes the
    recursive function as a parameter [rec] instead of calling itself
    directly, following the standard reified ITree cofixpoint pattern.
    The guardedness checker unfolds this transparent definition to verify
    that recursive calls are under Tau/Vis constructors. *)
Definition pass_body {R}
  (rec : itree ioE R -> itree ioE R)
  (ot : itreeF ioE R (itree ioE R)) : itree ioE R :=
  match ot with
  | RetF r => Ret r
  | TauF t' => Tau (rec t')
  | VisF e k => Vis e (fun x => rec (k x))
  end.

(** HOF-pattern cofixpoint: identity traversal that passes through all
    ITree nodes unchanged. In reified mode, the cofixpoint passes itself
    as a function value to [pass_body], not as a direct recursive call.
    Loopify classifies this as No_recursion (correct — ITree::run()
    handles iteration). Since itree is custom-extracted, [cofix_wrap]
    does not fire. The polymorphic type parameter [{R}] is needed so the
    translator generates a template function, ensuring the self-reference
    is a template instantiation expression. *)
Definition pass {R} : itree ioE R -> itree ioE R :=
  cofix pass_ t := pass_body pass_ (observe t).

(** Simple tree for testing: Ret 42 (no effects, no Tau). *)
Definition test_tree : itree ioE nat := Ret 42.
Crane Extract Inlined Constant test_tree => "ITree<unsigned int>::ret(42u)".

Definition test_count := count_taus 100 test_tree.

End LoopifyItreeReified.

Crane Extraction "loopify_itree_reified" LoopifyItreeReified.
