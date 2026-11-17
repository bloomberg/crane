From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Set Crane Loopify.

(** Tail modulo cons through a partner's body.

    [eb]'s tail call to [ea] continues in [ea]'s body, where [ea] calls [eb]
    under the constructor [Su]: [eb] is lowered tail modulo cons.  Normalize
    binds that call to a temporary, which Loopify puts back before reading
    the constructor around it, knowing a temporary by its name.  Inlining
    [ea] renamed every local of its body, the temporary too, so it was not
    put back, the transform found no constructor around the call and left it
    a call, and under [CRANE_CHECK_IR] the plan's chains were contradicted.
    [db] meets the same through [da]'s match on an enum. *)

Module LoopifyMutualTmcTemporary.

Inductive num := Z | Su (n : num).

Inductive color := Red | Green | Blue.

Fixpoint ea (n : num) : num :=
  match n with
  | Z => Z
  | Su m => Su (eb m (match m with Z => Z | Su k => k end))
  end
with eb (n : num) (x : num) : num :=
  match n with Z => x | Su m => ea m end.

Fixpoint da (c : color) (n : num) : num :=
  match n with
  | Z => Z
  | Su m => match c with Red => db m | Green => Su (db m) | Blue => da Red m end
  end
with db (n : num) : num :=
  match n with Z => Su Z | Su m => da Blue m end.

Fixpoint of_nat (n : nat) : num := match n with O => Z | S m => Su (of_nat m) end.

Fixpoint to_nat (n : num) : nat := match n with Z => O | Su m => S (to_nat m) end.

Definition run_ea (n : nat) : nat := to_nat (ea (of_nat n)).

Definition run_eb (n x : nat) : nat := to_nat (eb (of_nat n) (of_nat x)).

Definition run_da (c : color) (n : nat) : nat := to_nat (da c (of_nat n)).

Definition run_db (n : nat) : nat := to_nat (db (of_nat n)).

End LoopifyMutualTmcTemporary.

Crane Extraction "loopify_mutual_tmc_temporary" LoopifyMutualTmcTemporary.
