From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

(** KNOWN BUG: use-after-free in a loopified tail-recursive function.

    [rot] is tail recursive in two list arguments. Loopification picks a
    different representation for each loop variable:

      - [acc] is only ever passed on as a sub-field of the scrutinee, so it
        becomes a raw pointer:      [const lst *_loop_acc]
      - [l] is sometimes given a freshly built value, so it becomes an owning
        value:                      [lst _loop_l]

    The generated loop body is

      const auto &[a0, a1] = std::get<Cons>(_loop_l.v());
      const lst *_next_acc = crane_raw(a1);                 // points INTO _loop_l
      _loop_s = _loop_s + hd(deref _loop_acc);
      _loop_l = lst::cons(0, lst::cons(m, lst::nil()));     // frees the old _loop_l
      _loop_acc = _next_acc;                                // now dangling

    [_next_acc] aliases the tail cell owned by [_loop_l]. Overwriting
    [_loop_l] drops the last [shared_ptr] to that cell, so the pointer
    published into [_loop_acc] is dangling before the next iteration reads it
    through [hd].

    Expected: [go 6 = 21] (checked with [Compute] in Rocq).
    Actual:   7, plus an ASan heap-use-after-free.

    Without [Set Crane Loopify] the same file extracts to correct code. *)

Module LoopifyTailPtrAlias.

Inductive lst : Type :=
| nil : lst
| cons : nat -> lst -> lst.

Definition hd (l : lst) : nat :=
  match l with
  | nil => 0
  | cons x _ => x
  end.

Fixpoint rot (n : nat) (l : lst) (acc : lst) (s : nat) : nat :=
  match n with
  | O => s
  | S m =>
      match l with
      | nil => s
      | cons x t =>
          match x with
          | O => rot m (cons 0 (cons m nil)) t (s + hd acc)
          | S _ => s
          end
      end
  end.

Definition go (n : nat) : nat := rot n (cons 0 (cons 7 nil)) nil 0.

End LoopifyTailPtrAlias.

Crane Extraction "loopify_tail_ptr_alias" LoopifyTailPtrAlias.
