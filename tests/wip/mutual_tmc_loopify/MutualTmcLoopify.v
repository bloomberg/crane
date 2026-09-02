From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.

Module MutualTmcLoopify.

(** Mutual recursion whose recursive calls are under a constructor (TMC).
    [Crane Loopify] emits a [_Frame] worklist, but the body of the sibling
    [odds] is inlined as an immediately-invoked lambda that still calls
    [evens(...)] recursively, so the [while] loop runs exactly once and the
    real recursion is unchanged.  Compiles, then overflows the stack under
    ASan at moderate depth. *)

Inductive mylist := mnil | mcons : nat -> mylist -> mylist.

Fixpoint evens (n : nat) : mylist :=
  match n with
  | O => mnil
  | S k => mcons n (odds k)
  end
with odds (n : nat) : mylist :=
  match n with
  | O => mnil
  | S k => mcons n (evens k)
  end.

Fixpoint len (l : mylist) : nat :=
  match l with mnil => 0 | mcons _ r => S (len r) end.

End MutualTmcLoopify.

Crane Loopify MutualTmcLoopify.evens.
Crane Extraction "mutual_tmc_loopify" MutualTmcLoopify.evens MutualTmcLoopify.len.
