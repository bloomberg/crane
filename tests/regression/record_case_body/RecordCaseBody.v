(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*
   Extreme attempt to trigger TODOrecordProj by creating record match bodies
   that don't reduce to MLrel or MLapp(MLrel) patterns.

   Strategy: Create bodies that are MLcase, MLfix, MLletin, or other complex
   expressions that might not be recognized.
*)
Require Import Crane.Mapping.NatInt.
Require Crane.Extraction.

Module RecordCaseBody.

Record Rec := mkRec {
  f1 : nat;
  f2 : nat;
  f3 : nat
}.

(* Match on record, body is another match (MLcase?) *)
Definition case_in_body (r : Rec) : nat :=
  match r with
  | mkRec a b c =>
      (* Body is a case expression, not MLrel *)
      match a with
      | O => b + c
      | S n => n + b + c
      end
  end.

(* Recursive function in match body (MLfix?) *)
Fixpoint helper (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => n + helper n'
  end.

Definition fix_in_body (r : Rec) : nat :=
  match r with
  | mkRec a b c =>
      (* Body calls recursive function *)
      helper (a + b + c)
  end.

(* Let binding in match body (MLletin?) *)
Definition let_in_body (r : Rec) : nat :=
  match r with
  | mkRec a b c =>
      (* Complex let expression *)
      let x := a + b in
      let y := x + c in
      let z := y * 2 in
      match z with
      | O => 0
      | S _ => z
      end
  end.

(* Apply non-field function in body *)
Definition apply_nonfld (r : Rec) : nat :=
  match r with
  | mkRec a b c =>
      (* Apply external function, not field application *)
      S (S (a + b + c))
  end.

(* Conditional that doesn't reduce *)
Definition conditional_body (r : Rec) (flag : bool) : nat :=
  match r with
  | mkRec a b c =>
      (* Body has conditional *)
      if flag then
        match a with O => b | S _ => c end
      else
        a + b
  end.

(* Reference from outer scope in body *)
Definition outer_ref (x : nat) (r : Rec) : nat :=
  match r with
  | mkRec a b c =>
      (* References both field and outer variable *)
      x + a + b + c
  end.

(* Lambda in body *)
Definition lambda_body (r : Rec) : nat -> nat :=
  match r with
  | mkRec a b c =>
      (* Body is lambda, not direct field reference *)
      fun (n : nat) => n + a + b + c
  end.

(* Nested record match *)
Record RecRec := mkRecRec {
  inner : Rec;
  outer_field : nat
}.

Definition nested_record_match (rr : RecRec) : nat :=
  match rr with
  | mkRecRec r n =>
      (* Body matches on inner record *)
      match r with
      | mkRec a b c => a + b + c + n
      end
  end.

(* Global constant in body *)
Definition global_const := 42.

Definition global_in_body (r : Rec) : nat :=
  match r with
  | mkRec a b c =>
      (* Reference global constant *)
      global_const + a + b + c
  end.

(* Match with guard using fields *)
Definition guarded_body (r : Rec) : nat :=
  match r with
  | mkRec a b c =>
      if Nat.eqb a 0 then
        if Nat.eqb b 0 then c
        else b
      else a
  end.

(* Constructor in body *)
Definition constructor_body (r : Rec) : Rec :=
  match r with
  | mkRec a b c =>
      (* Build new record from fields *)
      mkRec (a + 1) (b + 1) (c + 1)
  end.

(* List operations in body *)
Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} _ _.

Fixpoint sum_list (l : list nat) : nat :=
  match l with
  | nil => 0
  | cons x xs => x + sum_list xs
  end.

Definition list_in_body (r : Rec) : nat :=
  match r with
  | mkRec a b c =>
      (* Build list from fields *)
      sum_list (cons a (cons b (cons c nil)))
  end.

Definition test1 := case_in_body (mkRec 1 2 3).
Definition test2 := fix_in_body (mkRec 4 5 6).
Definition test3 := let_in_body (mkRec 0 1 2).

End RecordCaseBody.

Crane Extraction "record_case_body" RecordCaseBody.
