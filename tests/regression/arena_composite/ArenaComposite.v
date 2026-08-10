(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Scoped-arena redesign regression: the composite-hang shape.

   A self-recursive value type ([expr]) is stored inside an FMapAVL-shaped
   persistent balanced tree ([avl]) whose [insert] rebalances (rotations copy
   whole subtrees, and thus copy the stored [expr] values, many times).  Under
   the old per-type arena representation this exact shape hung: a recursive
   field was a raw region pointer, so a value-copy had to deep-[arena_clone] the
   entire [expr] on every rebalance-triggered node copy, turning inserts into
   an explosion of full-subtree clones.

   With the scoped-arena redesign every recursive field is an ordinary
   refcounted smart pointer, so copying an [expr] (or an [avl] subtree) is an
   O(1) refcount bump -- the whole workload below must complete in bounded time
   with correct results, all inside a single [crane::arena_scope]. *)
From Stdlib Require Import PeanoNat.

Module Comp.

(* A self-recursive value type (stands in for the lexer's [regex]). *)
Inductive expr : Type :=
| lit : nat -> expr
| add : expr -> expr -> expr.

Fixpoint eval (e : expr) : nat :=
  match e with
  | lit n => n
  | add a b => eval a + eval b
  end.

Fixpoint esize (e : expr) : nat :=
  match e with
  | lit _ => 1
  | add a b => 1 + esize a + esize b
  end.

(* An FMapAVL-shaped persistent balanced tree keyed by [nat], storing an [expr]
   at every internal node.  [node l k v r h] carries a cached height [h]. *)
Inductive avl : Type :=
| leaf : avl
| node : avl -> nat -> expr -> avl -> nat -> avl.

Definition height (t : avl) : nat :=
  match t with
  | leaf => 0
  | node _ _ _ _ h => h
  end.

Definition mk (l : avl) (k : nat) (v : expr) (r : avl) : avl :=
  node l k v r (1 + Nat.max (height l) (height r)).

(* Single/double rotations: each reconstructs nodes, copying the [expr] values
   and subtrees they hold -- the copy path the old model deep-cloned. *)
Definition rotate_right (l : avl) (k : nat) (v : expr) (r : avl) : avl :=
  match l with
  | node ll lk lv lr _ => mk ll lk lv (mk lr k v r)
  | leaf => mk l k v r
  end.

Definition rotate_left (l : avl) (k : nat) (v : expr) (r : avl) : avl :=
  match r with
  | node rl rk rv rr _ => mk (mk l k v rl) rk rv rr
  | leaf => mk l k v r
  end.

Definition balance (l : avl) (k : nat) (v : expr) (r : avl) : avl :=
  let hl := height l in
  let hr := height r in
  if Nat.ltb (S (S hr)) hl then rotate_right l k v r
  else if Nat.ltb (S (S hl)) hr then rotate_left l k v r
  else mk l k v r.

Fixpoint insert (k : nat) (v : expr) (t : avl) : avl :=
  match t with
  | leaf => mk leaf k v leaf
  | node l k' v' r h =>
    if Nat.ltb k k' then balance (insert k v l) k' v' r
    else if Nat.ltb k' k then balance l k' v' (insert k v r)
    else node l k v r h
  end.

Fixpoint find (k : nat) (t : avl) : expr :=
  match t with
  | leaf => lit 0
  | node l k' v' r _ =>
    if Nat.ltb k k' then find k l
    else if Nat.ltb k' k then find k r
    else v'
  end.

Fixpoint size (t : avl) : nat :=
  match t with
  | leaf => 0
  | node l _ _ r _ => 1 + size l + size r
  end.

End Comp.

Require Crane.Extraction.
Crane Extraction "arena_composite" Comp.
