(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Mutual records — records referencing each other. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module MutualRecord.

(* Mutual inductive records: a company has departments, departments have employees *)
Inductive department : Type :=
  | mk_department : nat -> list employee -> department
with employee : Type :=
  | mk_employee : nat -> nat -> employee.

(* Accessors *)
Definition dept_id (d : department) : nat :=
  match d with mk_department id _ => id end.

Definition dept_employees (d : department) : list employee :=
  match d with mk_department _ emps => emps end.

Definition emp_id (e : employee) : nat :=
  match e with mk_employee id _ => id end.

Definition emp_salary (e : employee) : nat :=
  match e with mk_employee _ sal => sal end.

(* Mutual recursion over mutual types *)
Fixpoint dept_total_salary (d : department) : nat :=
  match d with
  | mk_department _ emps => emp_list_salary emps
  end
with emp_list_salary (l : list employee) : nat :=
  match l with
  | [] => 0
  | e :: rest => emp_salary e + emp_list_salary rest
  end.

Fixpoint dept_count (d : department) : nat :=
  match d with
  | mk_department _ emps => emp_list_count emps
  end
with emp_list_count (l : list employee) : nat :=
  match l with
  | [] => 0
  | _ :: rest => 1 + emp_list_count rest
  end.

(* === Test values === *)

Definition emp1 := mk_employee 1 50.
Definition emp2 := mk_employee 2 60.
Definition emp3 := mk_employee 3 70.
Definition test_dept := mk_department 100 [emp1; emp2; emp3].
Definition test_total_salary : nat := dept_total_salary test_dept.
Definition test_dept_count : nat := dept_count test_dept.
Definition test_dept_id : nat := dept_id test_dept.

End MutualRecord.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Crane Extraction "mutual_record" MutualRecord.
