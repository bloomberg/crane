From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Module NestedMatchClosure.

(** NESTED MATCH WITH CLOSURES

    BUG HYPOTHESIS: When two levels of pattern matching create
    structured bindings, and a closure in the inner match captures
    variables from BOTH levels, the outer bindings might be invalid
    by the time the closure is invoked.

    This is different from existing wip tests because:
    1. The captured variables come from MULTIPLE nesting levels
    2. The structured bindings from outer match may reference
       different shared_ptr nodes
    3. The inner match might consume/move its scrutinee, invalidating
       outer bindings that reference the same shared_ptr *)

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

(** Pattern 1: Nested match creating a closure that captures from both levels.
    The fixpoint [go] captures [outer_val] from outer match and
    [inner_val] from inner match. Both are structured binding refs. *)
Definition make_combiner (t : tree) : option (nat -> nat) :=
  match t with
  | Leaf => None
  | Node l outer_val r =>
    match l with
    | Leaf => Some (fun x => outer_val + x)
    | Node _ inner_val _ =>
      let combined := outer_val + inner_val in
      let fix go (x : nat) : nat :=
        match x with
        | O => combined
        | S x' => S (go x')
        end
      in Some go
    end
  end.

(** test1: Node (Node Leaf 10 Leaf) 20 Leaf
    outer_val = 20, l = Node Leaf 10 Leaf
    inner_val = 10, combined = 30
    go(5) = 30 + 5 = 35 *)
Definition test1 : nat :=
  match make_combiner (Node (Node Leaf 10 Leaf) 20 Leaf) with
  | Some f => f 5
  | None => 999
  end.

(** Pattern 2: Triple nesting *)
Definition make_deep_combiner (t : tree) : option (nat -> nat) :=
  match t with
  | Leaf => None
  | Node l1 v1 _ =>
    match l1 with
    | Leaf => None
    | Node l2 v2 _ =>
      match l2 with
      | Leaf => None
      | Node _ v3 _ =>
        let total := v1 + v2 + v3 in
        let fix go (x : nat) : nat :=
          match x with
          | O => total
          | S x' => S (go x')
          end
        in Some go
      end
    end
  end.

(** test2: Node (Node (Node Leaf 100 Leaf) 200 Leaf) 300 Leaf
    v1=300, v2=200, v3=100, total=600
    go(0) = 600 *)
Definition test2 : nat :=
  match make_deep_combiner (Node (Node (Node Leaf 100 Leaf) 200 Leaf) 300 Leaf) with
  | Some f => f 0
  | None => 999
  end.

(** Pattern 3: Closure capturing variables from match AND function param.
    The fixpoint captures BOTH pattern variables AND the function parameter.
    After the function returns, BOTH the pattern variables AND the
    function parameter are dead. *)
Definition make_param_combiner (t : tree) (base : nat) : option (nat -> nat) :=
  match t with
  | Leaf => None
  | Node l val r =>
    let fix go (x : nat) : nat :=
      match x with
      | O => base + val + tree_sum l + tree_sum r
      | S x' => S (go x')
      end
    in Some go
  end.

(** test3: Node (Node Leaf 5 Leaf) 10 (Node Leaf 15 Leaf), base=1000
    go(0) = 1000 + 10 + 5 + 15 = 1030
    go(3) = 1030 + 3 = 1033 *)
Definition test3 : nat :=
  match make_param_combiner (Node (Node Leaf 5 Leaf) 10 (Node Leaf 15 Leaf)) 1000 with
  | Some f => f 3
  | None => 999
  end.

(** Pattern 4: Store closure, THEN clobber stack with heavy computation *)
Definition test4 : nat :=
  let f := make_param_combiner (Node (Node Leaf 42 Leaf) 100 Leaf) 500 in
  (* Do some computation to clobber stack *)
  let noise1 := tree_sum (Node (Node (Node Leaf 1 Leaf) 2 Leaf) 3 (Node Leaf 4 Leaf)) in
  let noise2 := tree_sum (Node Leaf 999 (Node Leaf 888 Leaf)) in
  let _ := noise1 + noise2 in
  match f with
  | Some g => g 0
  | None => 999
  end.

End NestedMatchClosure.

Crane Extraction "nested_match_closure" NestedMatchClosure.
