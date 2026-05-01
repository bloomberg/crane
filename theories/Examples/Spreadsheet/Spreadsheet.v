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
*)

From Stdlib Require Import List BinInt.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.ZInt.
Import ListNotations.

Module Spreadsheet.

Open Scope int63.

(* Grid dimensions: a column is a letter A..Z and rows are 1..100. *)
Definition NUM_COLS : int := 26.
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

(* Total evaluator with fuel.  [None] means: out of fuel (e.g. cycle),
   or division by zero somewhere in the expression. *)
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

(* Smoke-test entry point used by the C++ harness during bring-up.
   Fills A1 = 2, B1 = 3, C1 = (A1 + B1) * 7, and returns C1's value. *)
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

End Spreadsheet.

Require Crane.Extraction.
Crane Extraction "Spreadsheet" Spreadsheet.
