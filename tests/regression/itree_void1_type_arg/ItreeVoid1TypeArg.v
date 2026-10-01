(** Crane bug: ITree's [void1] written as an explicit type argument is
    spelled [Void1], which is never declared, while the same type in a
    signature is spelled [std::any].

    Observed:
      static inline const Itree<std::any, Nat> u = ... wrap<Void1>(Nat::s(...));
    Diagnostics:
      error: use of undeclared identifier 'Void1'
      error: no matching constructor for initialization of 'const Itree<std::any, Nat>'

    Control: [t : itree void1 nat := Ret 3] with no polymorphic call in
    between compiles; the failure needs [void1] passed as a type argument.

    Reduced from Vellvm's vanilla-ITree extraction: the top-level
    [Vellvm.check : unit -> itree void1 bool] calls [ITree.iter] and
    [ITree.bind] at [void1] (seen as [ITree::template iter<Void1, ...>]). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.

Module ItreeVoid1TypeArg.
  Definition wrap {E : Type -> Type} (n : nat) : itree E nat := Ret n.
  Definition u : itree void1 nat := wrap 3.
  Definition is_three : bool :=
    match _observe u with RetF r => Nat.eqb r 3 | _ => false end.
End ItreeVoid1TypeArg.

Crane Extraction "itree_void1_type_arg" ItreeVoid1TypeArg.
