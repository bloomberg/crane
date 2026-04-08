From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module DoubleInvokeMove.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

(** wrap_with takes TWO args. Partial application creates a closure.
    Since t is stored in a constructor, wrap_with takes t as owned (by value). *)
Definition wrap_with (t : tree) (v : nat) : tree :=
  Node t v Leaf.

Definition left_value (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r =>
    match l with
    | Leaf => 0
    | Node _ lv _ => lv
    end
  end.

(** BUG HYPOTHESIS: partial application wrap_with t creates a [&] lambda.
    If t is marked dead-after (not used in continuation), std::move(t)
    appears INSIDE the lambda body. First call moves t, second call
    gets null → creates a node with null left child → left_value crashes.

    Expected: left_value(Node(t, 0, Leaf)) + left_value(Node(t, 1, Leaf))
            = left_value(t).left + left_value(t).left
            = 20 + 20 = 40  (the left_value of t = Node(Node(Leaf,10,Leaf),20,...) is 10,
              but left_value looks at l's first child... Actually let me recalculate.

    t = Node(Node(Leaf,10,Leaf), 20, Node(Leaf,30,Leaf))
    w1 = Node(t, 0, Leaf)
    left_value w1: match w1 → Node l v r where l=t, v=0, r=Leaf
                   match l=t → Node l2 v2 r2 where l2=Node(Leaf,10,Leaf), v2=20, r2=...
                   → v2 = 20
    w2 = Node(t, 1, Leaf)  [if t is still valid]
    left_value w2: same as w1 → 20
    Total: 40 *)
Definition bug_double_invoke : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let f := wrap_with t in
  let w1 := f 0 in
  let w2 := f 1 in
  left_value w1 + left_value w2.

End DoubleInvokeMove.

Crane Extraction "double_invoke_move" DoubleInvokeMove.
