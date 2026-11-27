(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*
   Try to create record patterns that don't reduce to simple MLrel patterns,
   potentially triggering the TODOrecordProj fallbacks.

   Strategy: Create matches where the body uses fields in non-trivial ways
   that might not simplify to MLrel during optimization.
*)
Require Import Crane.Mapping.NatInt.
From Stdlib Require Import Lia.
Require Crane.Extraction.

Module PathologicalRecord.

Record Rec := mkRec {
  f1 : nat;
  f2 : nat;
  f3 : nat
}.

(* Try to prevent simplification by using higher-order functions *)
Definition hof_access (r : Rec) : nat :=
  match r with
  | mkRec a b c =>
      (* Apply a function that takes the fields *)
      let g := fun (x : nat) (y : nat) (z : nat) => x + y + z in
      (* This might not simplify to MLrel *)
      (fun f => f a b c) g
  end.

(* Deeply nested lets that might confuse simplification *)
Definition nested_lets (r : Rec) : nat :=
  match r with
  | mkRec a b c =>
      let x1 := a in
      let x2 := let y1 := b in let y2 := y1 in y2 in
      let x3 := let z1 := let z2 := c in z2 in z1 in
      x1 + x2 + x3
  end.

(* Conditional logic that might create complex patterns *)
Definition conditional_access (r : Rec) (flag : bool) : nat :=
  match r with
  | mkRec a b c =>
      if flag then a + b else b + c
  end.

(* Recursive function using record fields *)
Fixpoint countdown (n : nat) (r : Rec) : nat :=
  match n with
  | O => match r with mkRec a _ _ => a end
  | S n' => match r with mkRec _ b _ => countdown n' r + b end
  end.

(* Match in match - double destructuring *)
Definition double_match (r1 r2 : Rec) : nat :=
  match r1 with
  | mkRec a1 b1 c1 =>
      match r2 with
      | mkRec a2 b2 c2 =>
          (* Use fields from both in a complex way *)
          let combine := fun x y z => (x + y) * z in
          combine (a1 + a2) (b1 + b2) (c1 + c2)
      end
  end.

(* Create a closure over record fields *)
Definition closure_over_fields (r : Rec) : nat -> nat :=
  match r with
  | mkRec a b c =>
      fun (x : nat) => x + a + b + c
  end.

Definition use_closure := closure_over_fields (mkRec 1 2 3) 10.

(* Pattern with guards (via if) *)
Definition guarded_pattern (r : Rec) : nat :=
  match r with
  | mkRec a b c =>
      if Nat.eqb a 0 then b + c
      else if Nat.eqb b 0 then a + c
      else a + b
  end.

(* Try to create index confusion with complex computations *)
Record BigRec := mkBigRec {
  bf1 : nat;
  prop1 : bf1 > 0;
  bf2 : nat;
  prop2 : bf2 > 0;
  bf3 : nat;
  prop3 : bf3 > 0;
  bf4 : nat;
  prop4 : bf4 > 0;
  bf5 : nat;
  prop5 : bf5 > 0
}.

(* Access fields in unusual order *)
Definition scrambled_access (r : BigRec) : nat :=
  match r with
  | mkBigRec a _ b _ c _ d _ e _ =>
      (* Access in reverse order *)
      e + d + c + b + a
  end.

(* Use some fields multiple times *)
Definition repeated_access (r : BigRec) : nat :=
  match r with
  | mkBigRec a _ b _ c _ d _ e _ =>
      a + a + b + b + c + c + d + d + e + e
  end.

Definition test1 := hof_access (mkRec 1 2 3).
Definition test2 := nested_lets (mkRec 4 5 6).
Definition test3 := double_match (mkRec 1 2 3) (mkRec 4 5 6).

End PathologicalRecord.

Crane Extraction "pathological_record" PathologicalRecord.
