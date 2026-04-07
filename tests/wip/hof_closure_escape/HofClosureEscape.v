From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module HofClosureEscape.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Definition sum_values (t : tree) (x : nat) : nat :=
  match t with
  | Leaf => x
  | Node l v r =>
    match l with
    | Leaf => v + x
    | Node _ lv _ =>
      match r with
      | Leaf => lv + x
      | Node _ rv _ => lv + rv + v + x
      end
    end
  end.

(** wrap_some is a helper that takes a function and wraps it in Some.
    The partial application happens at the CALL SITE of wrap_some,
    so the [&] lambda is created by the caller and passed through. *)
Definition wrap_some (f : nat -> nat) : option (nat -> nat) :=
  Some f.

(** BUG: The partial application sum_values t creates a [&] lambda.
    Even though wrap_some just passes f through to Some,
    the [&] lambda was created in hof_escape's stack frame.
    When hof_escape returns, captured t is destroyed. *)
Definition hof_escape (t : tree) : option (nat -> nat) :=
  wrap_some (sum_values t).

Definition apply_option (o : option (nat -> nat)) (x : nat) : nat :=
  match o with
  | None => x
  | Some f => f x
  end.

(** Clobber stack, then use the closure. *)
Definition bug_hof_escape : nat :=
  let t1 := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let o1 := hof_escape t1 in
  let t2 := Node (Node Leaf 77 Leaf) 88 (Node Leaf 99 Leaf) in
  let _ := hof_escape t2 in
  apply_option o1 0.

End HofClosureEscape.

Crane Extraction "hof_closure_escape" HofClosureEscape.
