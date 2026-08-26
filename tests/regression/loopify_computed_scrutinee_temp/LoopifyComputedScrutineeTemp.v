From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

(** Loopification bug: a raw pointer into a *computed scrutinee temporary*
    is stored in a stack frame that outlives the temporary.

    [walk] is non-tail recursive and matches on [wrap m l], a freshly
    computed value rather than a variable. Loopification binds it as a
    block-scoped temporary

      auto &&_sv = wrap(m, l);

    and then pushes the continuation frame

      _stack.emplace_back(_Enter{crane_raw(a1), m});

    where [a1] is a field of [_sv]. The frame outlives the block, so the
    next iteration reads [*_f.l] after [_sv] (and the cell it owned) has
    been destroyed. [hd l] then observes recycled heap memory: the reads
    happen after [wrap]'s two [make_shared] calls have reused the block,
    so the wrong answer shows up even without a sanitizer.

    Rocq: go n = 7*n + n*(n-1)/2. Extracted C++ under-counts for n >= 2.
    Removing [Set Crane Loopify.] makes the extracted code correct. *)

Module LoopifyComputedScrutineeTemp.

Inductive lst : Type :=
| nil : lst
| cons : nat -> lst -> lst.

Definition hd (l : lst) : nat := match l with nil => 0 | cons x _ => x end.

Definition wrap (m : nat) (l : lst) : lst := cons 7 (cons m l).

Fixpoint walk (n : nat) (l : lst) : nat :=
  match n with
  | O => 0
  | S m =>
      match wrap m l with
      | nil => 0
      | cons x t => x + hd l + walk m t
      end
  end.

Definition go (n : nat) : nat := walk n nil.

End LoopifyComputedScrutineeTemp.

Crane Extraction "loopify_computed_scrutinee_temp" LoopifyComputedScrutineeTemp.
