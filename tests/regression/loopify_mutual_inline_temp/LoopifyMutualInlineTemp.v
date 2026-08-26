From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

(** KNOWN BUG: use-after-free from loopifying mutual recursion.

    [even_step] and [odd_step] are mutually tail recursive. Loopification
    turns each into a single loop by inlining one step of its partner. The
    partner's list argument is a freshly built value, so it is materialised as
    a block-scoped temporary bound to a const reference:

      const lst &_inl_l = lst::cons(a0 + 1, lst::nil());
      ...
      const auto &[a0, a1] = std::get<Cons>(_inl_l.v());
      _loop_s    = _inl_s + a0;
      _loop_keep = crane_raw(a1);        // points INTO the temporary
      _loop_l    = lst::cons(a0, lst::cons(a0, lst::nil()));
      _loop_n    = m;

    [_loop_keep] is published out of the loop body while pointing at a cell
    owned solely by [_inl_l]. Lifetime extension only keeps that temporary
    alive to the end of the enclosing block, so it dies at the end of the
    iteration and [_loop_keep] dangles before the next iteration reads it
    through [hd].

    Expected: [go 8 = 16], [go 7 = 12] (checked with [Compute] in Rocq).
    Actual:   [go 8] returns 12, plus an ASan heap-use-after-free.

    Without [Set Crane Loopify] the same file extracts to correct code. *)

Module LoopifyMutualInlineTemp.

Inductive lst : Type :=
| nil : lst
| cons : nat -> lst -> lst.

Fixpoint build (n : nat) (acc : lst) : lst :=
  match n with O => acc | S m => build m (cons n acc) end.

Definition hd (l : lst) : nat := match l with nil => 0 | cons x _ => x end.

Fixpoint even_step (n : nat) (l : lst) (keep : lst) (s : nat) {struct n} : nat :=
  match n with
  | O => s + hd keep
  | S m =>
      match l with
      | nil => s
      | cons x t => odd_step m (cons x (cons x nil)) t (s + x)
      end
  end
with odd_step (n : nat) (l : lst) (keep : lst) (s : nat) {struct n} : nat :=
  match n with
  | O => s + hd keep
  | S m =>
      match l with
      | nil => s
      | cons x t => even_step m (cons (x + 1) nil) t (s + hd keep)
      end
  end.

Definition go (n : nat) : nat := even_step n (build 4 nil) nil 0.

End LoopifyMutualInlineTemp.

Crane Extraction "loopify_mutual_inline_temp" LoopifyMutualInlineTemp.
