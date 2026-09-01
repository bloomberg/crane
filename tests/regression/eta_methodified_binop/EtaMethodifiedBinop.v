(** A binary function passed as an argument, where the callee has been
    methodified onto its first argument.  The eta wrapper Crane builds takes
    only one parameter and calls the method with no arguments at all:

    {v
      [](const auto &_x) { return _x.eqb(); }
      no matching function for call to 'count'
    v} *)

Require Crane.Extraction.

Module EtaMethodifiedBinop.

Section Sec.
Variable A : Type.
Variable eqb : A -> A -> bool.

Fixpoint count (x : A) (l : list A) : nat :=
  match l with
  | nil => 0
  | cons y r => if eqb x y then S (count x r) else count x r
  end.
End Sec.

Definition test : nat := count nat Nat.eqb 1 (cons 1 nil).

End EtaMethodifiedBinop.

Crane Extraction "eta_methodified_binop" EtaMethodifiedBinop.
