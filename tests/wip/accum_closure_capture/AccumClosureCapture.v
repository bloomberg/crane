From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module AccumClosureCapture.

(** Define fn_list BEFORE tree so fn_list is not a forward inductive.
    This lets extract_closures (tree -> fn_list) be methodified on tree,
    because fn_list in the return type is not blocked by forward-ref check. *)

Inductive fn_list :=
  | FNil : fn_list
  | FCons : (nat -> nat) -> fn_list -> fn_list.

Inductive tree : Type :=
  | Leaf : tree
  | Node : tree -> nat -> tree -> tree.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

Fixpoint apply_all (fs : fn_list) (init : nat) : nat :=
  match fs with
  | FNil => init
  | FCons f rest => apply_all rest (f init)
  end.

(** BUG HYPOTHESIS: extract_closures is methodified on tree. The closures
    capture this (for tree_sum t) as a raw pointer. They are stored in
    fn_list. After extract_closures returns, the temporary tree is destroyed.
    Calling the closures from apply_all dereferences dangling this. *)

Definition extract_closures (t : tree) : fn_list :=
  match t with
  | Leaf => FNil
  | Node l v r =>
    FCons (fun x => x + tree_sum t)
      (FCons (fun x => x + v)
        (FCons (fun x => x + tree_sum t) FNil))
  end.

(** test1: Create tree with sum=42, extract closures, apply to 0.
    Expected: 0 + 42 = 42, 42 + 20 = 62, 62 + 42 = 104.
    With dangling this, tree_sum reads garbage. *)
Definition test1 : nat :=
  let fs := extract_closures (Node (Node Leaf 10 Leaf) 20 (Node Leaf 12 Leaf)) in
  apply_all fs 0.

(** test2: Allocate a noise tree between extracting closures and applying them.
    Increases memory pressure on freed region. *)
Definition test2 : nat :=
  let fs := extract_closures (Node Leaf 100 Leaf) in
  let noise := tree_sum (Node Leaf 999 Leaf) in
  apply_all fs noise.

(** test2 expected: noise = 999.
    999 + 100 = 1099, 1099 + 100 = 1199, 1199 + 100 = 1299.
    Wait: the closures capture tree_sum t where sum(t)=100 and v=100.
    apply_all: FCons (fun x => x + tree_sum t) ... so:
    999 + 100 = 1099, 1099 + 100 = 1199, 1199 + 100 = 1299. *)

End AccumClosureCapture.

Crane Extraction "accum_closure_capture" AccumClosureCapture.
