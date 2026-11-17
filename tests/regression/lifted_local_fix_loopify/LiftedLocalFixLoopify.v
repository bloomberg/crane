(** A local fixpoint polymorphic in a type its enclosing definition does
    not quantify over is lifted out into a helper of its own, and under
    [Set Crane Loopify] that helper is loopified like any function.  Its
    recursion has to be planned from the fixpoint it came from: the helper
    is not a declaration of the program, so a plan of declarations alone
    does not know it.  [len] is tail recursive, [sum_all] is not. *)

From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

Set Crane Loopify.

Module LiftedLocalFixLoopify.

Definition total_length (l : list (list nat)) : nat :=
  let fix len {A : Type} (xs : list A) (acc : nat) : nat :=
    match xs with
    | [] => acc
    | _ :: t => len t (S acc)
    end
  in
  len l 0 + len (concat l) 0.

Definition weighted (l : list (list nat)) : nat :=
  let fix sum_all {A : Type} (w : A -> nat) (xs : list A) : nat :=
    match xs with
    | [] => 0
    | x :: t => w x + sum_all w t
    end
  in
  sum_all (fun xs => sum_all (fun n => n) xs) l + sum_all (fun _ => 1) l.

End LiftedLocalFixLoopify.

Crane Extraction "lifted_local_fix_loopify" LiftedLocalFixLoopify.
