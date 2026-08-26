From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

(** KNOWN BUG: self-assignment of a loop variable from its own sub-field.

    [drain] is tail recursive. One branch passes a freshly built list, so the
    loop variable for [l] has to be an owning value rather than a pointer; the
    other branch passes the scrutinee's own tail, which loopification emits as
    a direct self-assignment:

      const auto &[a0, a1] = std::get<Cons>(_loop_l.v());
      _loop_s  = _loop_s + a0;
      _loop_l  = *a1;        // source is owned by _loop_l itself

    [_loop_l] is the sole owner of the cell [a1] points at, so the assignment
    destroys its own source. When the source cell uses a *different*
    constructor than the destination ([One] vs [Cons]), std::variant's
    assignment path is destroy-then-construct: it runs [~Cons], which drops
    the last shared_ptr to the [One] cell, and then copy-constructs [One] out
    of the freed cell.

    A three-constructor inductive is what makes this visible: with only two
    constructors the surviving alternative is the empty [Nil], so nothing is
    read back out of the freed storage.

    Expected: [go 8 = 20], [go 12 = 42] (checked with [Compute] in Rocq).
    Actual:   both return 2, plus an ASan heap-use-after-free.

    Without [Set Crane Loopify] the same file extracts to correct code. *)

Module LoopifyVariantSelfAssign.

Inductive lst : Type :=
| nil : lst
| one : nat -> lst
| cons : nat -> lst -> lst.

Fixpoint drain (n : nat) (l : lst) (s : nat) : nat :=
  match n with
  | O => s
  | S m =>
      match l with
      | nil => s
      | one k => drain m (cons k (one (k + 1))) (s + k)
      | cons x t => drain m t (s + x)
      end
  end.

Definition go (n : nat) : nat := drain n (one 1) 0.

End LoopifyVariantSelfAssign.

Crane Extraction "loopify_variant_self_assign" LoopifyVariantSelfAssign.
