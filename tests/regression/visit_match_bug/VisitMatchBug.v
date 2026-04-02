(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Bugs in std::visit and record pattern match field access *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module VisitMatchBug.

(* ===== FROM VisitBug.v ===== *)
(* Use a non-record inductive so it uses std::visit, not record optimization *)
Inductive Tree : Type :=
  | Leaf : nat -> Tree
  | Node : Tree -> nat -> Tree -> Tree.

(* BUG TRIGGER: Match on owned parameter (consumed/returned)
   If Tree is passed by value (owned), the scrutinee might be moved.
   std::visit is called with: std::visit(Overloaded{...}, scrut->v())
   If scrut is std::move(t), we get: std::move(t)->v()  (USE-AFTER-MOVE!)
*)

(* Helper that consumes tree *)
Definition consume (t : Tree) : Tree := t.

(* Match on consumed parameter *)
Definition match_after_consume (t : Tree) : nat :=
  let t2 := consume t in
  match t2 with
  | Leaf n => n
  | Node l v r => v
  end.

(* Match on last-use parameter *)
Definition match_last_use (t : Tree) : nat :=
  match t with
  | Leaf n => n
  | Node l v r => v
  end.

(* Nested match - inner match on consumed value *)
Definition nested_match_consume (t : Tree) : nat :=
  let t2 := consume t in
  let x := match t2 with
           | Leaf n => n
           | Node l v r => v
           end in
  x.

(* Match in tail position after let chain *)
Definition chain_then_match (t1 : Tree) : nat :=
  let t2 := consume t1 in
  let t3 := consume t2 in
  match t3 with
  | Leaf n => n
  | Node l v r => v
  end.

(* ===== FROM MatchBug.v ===== *)
Record State : Type := mkState {
  value : nat;
  data : nat
}.

(* BUG TRIGGER: Pattern match that extracts a field
   This becomes: match s with mkState v d => v end
   Without fix, translation.ml:2206 generates:
     gen_expr env t  where t is the scrutinee s
   If s is marked for move, this generates CPPmove(s), then
   make_field_access wraps it: CPPget'(CPPmove(s), value)
   Which prints as: std::move(s)->value  (USE-AFTER-MOVE!)
*)
Definition match_extract_field (s : State) : nat :=
  match s with
  | mkState v d => v
  end.

(* Variant: extract multiple fields *)
Definition match_extract_two (s : State) : nat :=
  match s with
  | mkState v d => v + d
  end.

(* Variant: nested match *)
Definition match_nested (s : State) : nat :=
  match s with
  | mkState v d =>
      match mkState v d with
      | mkState v2 d2 => v2
      end
  end.

(* Variant: match in tail position *)
Definition match_in_tail (s : State) : nat :=
  let x := s in
  match x with
  | mkState v d => v
  end.

(* Variant: match result used in expression *)
Definition match_in_expr (s : State) : nat :=
  (match s with mkState v d => v end) + 1.

End VisitMatchBug.

Crane Extraction "visit_match_bug" VisitMatchBug.
