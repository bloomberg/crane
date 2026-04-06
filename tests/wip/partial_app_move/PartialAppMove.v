From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module PartialAppMove.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

(** A function taking two args: tree -> nat -> nat.
    Partial application of this to a tree creates a
    closure nat -> nat in C++ via [&] lambda. *)
Definition sum_values (t : tree) : nat -> nat :=
  match t with
  | Leaf => fun x => x
  | Node l v r =>
    match l with
    | Leaf => fun x => v + x
    | Node _ lv _ =>
      match r with
      | Leaf => fun x => lv + x
      | Node _ rv _ => fun x => lv + rv + v + x
      end
    end
  end.

(** Wrap a tree inside another Node.
    In C++, this calls tree::node() which has rvalue ref overloads.
    If escape analysis adds std::move(t) here, the move is REAL. *)
Definition wrap (t : tree) : tree :=
  Node t 0 Leaf.

(** BUG TRIGGER: partial application creates a [&] lambda capturing t,
    then t is passed to a constructor (actually moved via rvalue ref),
    then the lambda accesses the moved-from t. *)
Definition trigger_bug (t : tree) : nat :=
  let f := sum_values t in
  let w := wrap t in
  match w with
  | Leaf => f 0
  | Node _ _ _ => f 99
  end.

(** Build a tree and trigger the bug. *)
Definition run_bug : nat :=
  trigger_bug (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf)).

(** Inline version: t is a local variable, not a function parameter.
    This is where move optimization might actually move t. *)
Definition inline_bug : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let f := sum_values t in
  let w := Node t 42 Leaf in
  match w with
  | Leaf => f 0
  | Node _ _ _ => f 99
  end.

(** Same but using wrap function. *)
Definition inline_bug2 : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let f := sum_values t in
  let w := wrap t in
  match w with
  | Leaf => f 0
  | Node _ _ _ => f 99
  end.

End PartialAppMove.

Crane Extraction "partial_app_move" PartialAppMove.
