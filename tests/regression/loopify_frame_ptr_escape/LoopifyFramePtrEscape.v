From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

(** KNOWN BUG: use-after-free in a loopified *non-tail* recursive function.

    [walk] is not tail recursive, so loopification builds an explicit frame
    stack. Within one [_Enter] frame, the two list parameters again get
    different representations:

      struct _Enter { const lst *acc; lst l; uint64_t n; };

    [acc] is a raw pointer (it is always passed a sub-field), [l] is owned by
    value (it is sometimes given a freshly built value). The recursive call
    pushes

      _stack.emplace_back(_Enter{
          crane_raw(a1),                                   // points INTO this frame's l
          lst::cons(m + 1, lst::cons(m, lst::nil())),      // fresh l for the callee
          m});

    The [acc] pointer aliases a cell owned by the *current* iteration's
    [_f.l]. [_f] is a loop-body local, so it is destroyed at the end of the
    iteration, dropping the last reference to that cell. The frame just pushed
    keeps the now-dangling pointer and dereferences it later via [hd acc].

    Expected: [go 4 = 15] (checked with [Compute] in Rocq).
    Actual:   14, plus an ASan heap-use-after-free.

    Without [Set Crane Loopify] the same file extracts to correct code. *)

Module LoopifyFramePtrEscape.

Inductive lst : Type :=
| nil : lst
| cons : nat -> lst -> lst.

Definition hd (l : lst) : nat :=
  match l with
  | nil => 0
  | cons x _ => x
  end.

Fixpoint walk (n : nat) (l : lst) (acc : lst) : nat :=
  match n with
  | O => hd acc
  | S m =>
      match l with
      | nil => 0
      | cons x t => x + walk m (cons (S m) (cons m nil)) t
      end
  end.

Definition go (n : nat) : nat := walk n (cons 5 (cons 7 nil)) nil.

End LoopifyFramePtrEscape.

Crane Extraction "loopify_frame_ptr_escape" LoopifyFramePtrEscape.
