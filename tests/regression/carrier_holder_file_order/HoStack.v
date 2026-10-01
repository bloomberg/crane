From ITree Require Import ITree.
From CraneTestsRegression Require Import carrier_holder_file_order.HoEvents.
Definition stateT (S : Type) (M : Type -> Type) (A : Type) : Type := S -> M (prod S A).
Section WithParams.
  Context {Pa : Params}.
  Definition get_st (n : nat) : stateT nat (itree AllE) nat := fun s => Ret (s + n, s).
End WithParams.
