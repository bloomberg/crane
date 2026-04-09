From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ClosureChain.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

(** Build a chain of closures via recursion.
    Each level wraps the previous closure in a new one.

    make_chain 0 t = fun x => tree_sum t + x
    make_chain 1 t = fun x => (fun x => tree_sum t + x) (x + 1)
    make_chain n t = fun x => (make_chain (n-1) t) (x + 1)

    BUG HYPOTHESIS: make_chain (S n') t creates a local binding
    f := make_chain n' t, then returns fun x => f (x + 1).
    If f is captured by [&], it dies when make_chain returns. *)
Fixpoint make_chain (n : nat) (t : tree) : nat -> nat :=
  match n with
  | 0 => fun x => tree_sum t + x
  | S n' =>
    let f := make_chain n' t in
    fun x => f (x + 1)
  end.

(** Test: make_chain 0 t 5 = tree_sum(t) + 5 = 10 + 5 = 15 *)
Definition chain_0 : nat :=
  let t := Node Leaf 10 Leaf in
  make_chain 0 t 5.

(** Test: make_chain 1 t 5 = (make_chain 0 t) (5 + 1) = 10 + 6 = 16 *)
Definition chain_1 : nat :=
  let t := Node Leaf 10 Leaf in
  make_chain 1 t 5.

(** Test: make_chain 3 t 0 = (make_chain 0 t) 3 = 10 + 3 = 13 *)
Definition chain_3 : nat :=
  let t := Node Leaf 10 Leaf in
  make_chain 3 t 0.

(** Store the chain result and call it twice.
    If make_chain returns a chain with dangling references,
    the second call through clobbered stack would give wrong result. *)
Definition chain_double_call : nat :=
  let t := Node Leaf 10 Leaf in
  let f := make_chain 2 t in
  f 0 + f 100.

End ClosureChain.

Crane Extraction "closure_chain" ClosureChain.
