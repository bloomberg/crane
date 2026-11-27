(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Recursive records — self-referential fields. *)

From Stdlib Require Import Nat Bool List.
Import ListNotations.

Module RecRecord.

(* === Recursive record: linked list as record === *)

Inductive rlist (A : Type) : Type :=
  | rnil : rlist A
  | rcons : A -> rlist A -> rlist A.

Arguments rnil {A}.
Arguments rcons {A} _ _.

Inductive RNode := mkRNode {
  rn_value : nat;
  rn_next : option RNode
}.

(* === Mutually referencing records === *)

Record Employee := mkEmployee {
  emp_name : nat;  (* using nat as ID *)
  emp_dept : nat
}.

Record Department := mkDepartment {
  dept_id : nat;
  dept_head : Employee;
  dept_size : nat
}.

(* === Recursive function over self-referential structure === *)

Fixpoint rlist_length {A : Type} (l : rlist A) : nat :=
  match l with
  | rnil => 0
  | rcons _ rest => S (rlist_length rest)
  end.

Fixpoint rlist_sum (l : rlist nat) : nat :=
  match l with
  | rnil => 0
  | rcons x rest => x + rlist_sum rest
  end.

Fixpoint rnode_depth (r : RNode) : nat :=
  match rn_next r with
  | None => 1
  | Some next => S (rnode_depth next)
  end.

(* === Test values === *)

Definition test_rlist : rlist nat := rcons 1 (rcons 2 (rcons 3 rnil)).
Definition test_rlist_len : nat := rlist_length test_rlist.
Definition test_rlist_sum : nat := rlist_sum test_rlist.

Definition test_rnode : RNode :=
  mkRNode 1 (Some (mkRNode 2 (Some (mkRNode 3 None)))).
Definition test_rnode_depth : nat := rnode_depth test_rnode.

Definition test_emp : Employee := mkEmployee 42 7.
Definition test_dept : Department := mkDepartment 7 test_emp 50.
Definition test_dept_head_name : nat := emp_name (dept_head test_dept).

End RecRecord.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.
Crane Extraction "rec_record" RecRecord.
