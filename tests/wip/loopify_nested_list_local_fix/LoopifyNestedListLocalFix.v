(** Found by Ephyra round 24 (under [CRANE_LOOPIFY_CENSUS], which turns
    Loopify on everywhere; [Set Crane Loopify] alone is enough). Under
    Loopify, a non-tail recursion building a nested inductive
    ([mterm], whose constructor takes a [list mterm]) whose list argument
    holds, next to the recursive call, a local fixpoint call ([h]) or a
    [fold_left] ([h2]).  Without Loopify it extracts and runs.

    Expected: extracts; [size (h 3) = 7], [size (h2 3) = 10].
    Actual: Anomaly "Crane: a declaration reached the printer holding a
    capture that runs in place, which only a lowered declaration may hold
    in LoopifyNestedListLocalFix.h"; for [h2] alone, "... holding a stored
    capture ...".  The generator found both (the second under BDE). *)
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Extraction.
From Stdlib Require Import List.
Import ListNotations.

Set Crane Loopify.

Module LoopifyNestedListLocalFix.

Inductive mterm : Type := MLit : nat -> mterm | MAdd : mterm -> list mterm -> mterm.

Fixpoint h (n : nat) : mterm :=
  match n with
  | O => MLit 0
  | S m =>
    MAdd (h m)
      [let fix go (l : list nat) {struct l} : mterm :=
         match l with [] => MLit 1 | _ :: r => go r end
       in go []]
  end.

Fixpoint h2 (n : nat) : mterm :=
  match n with
  | O => MLit 0
  | S m => MAdd (h2 m) [MLit 0; fold_left (fun (acc : mterm) (_ : bool) => acc) [true] (MLit 0)]
  end.

Fixpoint size (t : mterm) : nat :=
  match t with
  | MLit _ => 1
  | MAdd a l => S (size a + fold_right (fun x acc => size x + acc) 0 l)
  end.

Definition result : nat := size (h 3) * 100 + size (h2 3).

End LoopifyNestedListLocalFix.

Crane Extraction "loopify_nested_list_local_fix" LoopifyNestedListLocalFix.
