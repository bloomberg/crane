From Crane Require Extraction.

Module FunctionReturnBranchProbe.

(** A recursive function whose match branches return different lambda
    expressions.  Crane generates an inner lambda with no explicit return type,
    causing C++ to fail to deduce a common return type across the two distinct
    closure types. *)
Fixpoint make_adder (n : nat) : nat -> nat :=
  match n with
  | 0 => fun x => x
  | S n' =>
      let f := make_adder n' in
      fun x => S (f x)
  end.

Definition sample : nat := make_adder 2 40.

End FunctionReturnBranchProbe.

Crane Extraction "function_return_branch_probe" FunctionReturnBranchProbe.
