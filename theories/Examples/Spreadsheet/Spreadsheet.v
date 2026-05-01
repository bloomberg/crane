(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Spreadsheet model.

   A small spreadsheet kernel intended to be extracted with Crane and
   driven by a Dear ImGui front-end (see [bin/spreadsheet/]).

   Cells hold either nothing, a signed integer literal, or a formula
   tree of arithmetic over cell references.  The evaluator is total:
   it consumes a [fuel] argument and returns [None] when the formula
   diverges (out of fuel, or division by zero).

   Extraction lives in [bin/spreadsheet/Spreadsheet.v] (for the
   front-end binary) and [tests/basics/spreadsheet/Spreadsheet.v]
   (for the regression test).  This file holds the model only.
*)

From Stdlib Require Import List BinInt.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.ZInt.
Import ListNotations.

Module Spreadsheet.

Open Scope int63.

(* Grid dimensions: 104 columns (A..CZ) by 100 rows. *)
Definition NUM_COLS : int := 104.
Definition NUM_ROWS : int := 100.
Definition GRID_SIZE : int := PrimInt63.mul NUM_COLS NUM_ROWS.

Record CellRef : Type := mkRef
  { ref_col : int
  ; ref_row : int }.

(* Linearise a (col, row) reference into the underlying array index. *)
Definition cell_index (r : CellRef) : int :=
  PrimInt63.add (PrimInt63.mul (ref_row r) NUM_COLS) (ref_col r).

(* Expression AST.  Cell values are signed integers ([Z]); refs index
   other cells; arithmetic is the four basic operators with parentheses
   handled by the AST shape. *)
Inductive Expr : Type :=
  | EInt : Z -> Expr
  | ERef : CellRef -> Expr
  | EAdd : Expr -> Expr -> Expr
  | ESub : Expr -> Expr -> Expr
  | EMul : Expr -> Expr -> Expr
  | EDiv : Expr -> Expr -> Expr.

Inductive Cell : Type :=
  | CEmpty : Cell
  | CLit   : Z -> Cell
  | CForm  : Expr -> Cell.

Definition Sheet : Type := PrimArray.array Cell.

Definition new_sheet : Sheet :=
  PrimArray.make GRID_SIZE CEmpty.

Definition get_cell (s : Sheet) (r : CellRef) : Cell :=
  PrimArray.get s (cell_index r).

Definition set_cell (s : Sheet) (r : CellRef) (c : Cell) : Sheet :=
  PrimArray.set s (cell_index r) c.

(* Total evaluator with fuel.  [None] means: out of fuel (e.g. a
   reference cycle), or division by zero somewhere in the expression. *)
Fixpoint eval_expr (fuel : nat) (s : Sheet) (e : Expr) : option Z :=
  match fuel with
  | O => None
  | S fuel' =>
    match e with
    | EInt n => Some n
    | ERef r =>
      match get_cell s r with
      | CEmpty => Some 0%Z
      | CLit n => Some n
      | CForm e' => eval_expr fuel' s e'
      end
    | EAdd a b =>
      match eval_expr fuel' s a, eval_expr fuel' s b with
      | Some va, Some vb => Some (Z.add va vb)
      | _, _ => None
      end
    | ESub a b =>
      match eval_expr fuel' s a, eval_expr fuel' s b with
      | Some va, Some vb => Some (Z.sub va vb)
      | _, _ => None
      end
    | EMul a b =>
      match eval_expr fuel' s a, eval_expr fuel' s b with
      | Some va, Some vb => Some (Z.mul va vb)
      | _, _ => None
      end
    | EDiv a b =>
      match eval_expr fuel' s a, eval_expr fuel' s b with
      | Some va, Some vb =>
        if Z.eqb vb 0%Z then None else Some (Z.div va vb)
      | _, _ => None
      end
    end
  end.

Definition eval_cell (fuel : nat) (s : Sheet) (r : CellRef) : option Z :=
  match get_cell s r with
  | CEmpty => Some 0%Z
  | CLit n => Some n
  | CForm e => eval_expr fuel s e
  end.

Definition DEFAULT_FUEL : nat := 1000.

(* Smoke value used by harness code during bring-up.  Fills A1=2, B1=3,
   then computes C1 = (A1+B1) * 7. *)
Definition smoke : option Z :=
  let a1 := mkRef 0 0 in
  let b1 := mkRef 1 0 in
  let c1 := mkRef 2 0 in
  let s0 := new_sheet in
  let s1 := set_cell s0 a1 (CLit 2%Z) in
  let s2 := set_cell s1 b1 (CLit 3%Z) in
  let s3 := set_cell s2 c1
    (CForm (EMul (EAdd (ERef a1) (ERef b1)) (EInt 7%Z))) in
  eval_cell DEFAULT_FUEL s3 c1.

(* --- Theorems --------------------------------------------------------

   The model is a kernel — most of its theorems are statements about
   the evaluator's behaviour on individual cell shapes.  We prove a
   handful here; richer properties (frame preservation under [set_cell],
   acyclicity bounds) live in a future iteration. *)

(* The smoke value computes to [Some 35].  The proof is a closed
   computation: vm_compute reduces through PrimArray's primitives and
   the fuel-bounded recursion. *)
Theorem smoke_computes : smoke = Some 35%Z.
Proof. vm_compute. reflexivity. Qed.

(* Reading an empty cell returns 0, regardless of fuel. *)
Theorem eval_empty : forall s r fuel,
  get_cell s r = CEmpty -> eval_cell fuel s r = Some 0%Z.
Proof. intros s r fuel H. unfold eval_cell. rewrite H. reflexivity. Qed.

(* Reading a literal cell returns the literal, regardless of fuel. *)
Theorem eval_lit : forall s r n fuel,
  get_cell s r = CLit n -> eval_cell fuel s r = Some n.
Proof. intros s r n fuel H. unfold eval_cell. rewrite H. reflexivity. Qed.

(* A cell whose formula references itself exhausts any fuel and returns
   [None].  This is a closed computation: pick a concrete sheet whose
   only filled cell is the self-reference, then [vm_compute]. *)
Theorem eval_self_cycle_diverges :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r (CForm (ERef r)) in
  eval_cell DEFAULT_FUEL s r = None.
Proof. vm_compute. reflexivity. Qed.

(* Division by zero in a formula returns [None]. *)
Theorem eval_divzero :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EDiv (EInt 1%Z) (EInt 0%Z))) in
  eval_cell DEFAULT_FUEL s r = None.
Proof. vm_compute. reflexivity. Qed.

End Spreadsheet.
