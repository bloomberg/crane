From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module FixFoldEscape.

(** Manual fold_left to avoid stdlib extraction complications. *)
Fixpoint fold_left (f : list (nat -> nat) -> nat -> list (nat -> nat))
                   (acc : list (nat -> nat))
                   (l : list nat) : list (nat -> nat) :=
  match l with
  | nil => acc
  | cons h t => fold_left f (f acc h) t
  end.

(** Collect fixpoint closures by folding over a list of nats.
    Each iteration creates a new fixpoint [adder] that captures the
    current element [n] from the fold callback's parameter.

    BUG HYPOTHESIS: The callback lambda's parameter [n] lives on the
    callback's stack frame. The fixpoint [adder] captures [n] by [&].
    The callback returns [cons adder acc], storing the closure.
    After the callback returns, [n] is destroyed. Later iterations and
    the final result contain dangling closures. *)

Definition collect_adders (l : list nat) : list (nat -> nat) :=
  fold_left (fun acc n =>
    let fix adder (x : nat) : nat :=
      match x with
      | O => n
      | S x' => S (adder x')
      end
    in cons adder acc
  ) nil l.

Definition apply_head (l : list (nat -> nat)) (x : nat) : nat :=
  match l with
  | nil => 0
  | cons f _ => f x
  end.

Fixpoint sum_apply (l : list (nat -> nat)) (x : nat) : nat :=
  match l with
  | nil => 0
  | cons f rest => f x + sum_apply rest x
  end.

(** test1: collect_adders [10; 20; 30] -> [adder_30; adder_20; adder_10]
    (reversed by fold_left). apply_head picks adder_30, apply to 5 -> 35. *)
Definition test1 : nat :=
  apply_head (collect_adders (cons 10 (cons 20 (cons 30 nil)))) 5.

(** test2: Sum all adders applied to 0.
    adder_30(0) + adder_20(0) + adder_10(0) = 30 + 20 + 10 = 60. *)
Definition test2 : nat :=
  sum_apply (collect_adders (cons 10 (cons 20 (cons 30 nil)))) 0.

(** test3: With noise between collection and use. *)
Definition test3 : nat :=
  let fns := collect_adders (cons 100 (cons 200 nil)) in
  let noise := 55 + 44 + 33 in
  apply_head fns 0 + noise.

End FixFoldEscape.

Crane Extraction "fix_fold_escape" FixFoldEscape.
