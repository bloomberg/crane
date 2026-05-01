(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Spreadsheet model.

   A small spreadsheet kernel intended to be extracted with Crane and
   driven by a Dear ImGui front-end (see [bin/spreadsheet/]).

   Cells hold either nothing, a signed integer literal, or a formula
   tree of arithmetic over cell references.  The evaluator is total:
   it consumes a fuel parameter (a generous safety cap) and a
   "visited" path so reference cycles are detected explicitly rather
   than mistaken for legitimate deep formulas.

   Extraction lives in [bin/spreadsheet/Spreadsheet/Spreadsheet.v]
   (for the front-end binary) and
   [tests/basics/spreadsheet/Spreadsheet.v] (for the regression
   test).  This file holds the model only.
*)

From Stdlib Require Import List BinInt PArray.
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

Definition cellref_eqb (r1 r2 : CellRef) : bool :=
  andb (PrimInt63.eqb (ref_col r1) (ref_col r2))
       (PrimInt63.eqb (ref_row r1) (ref_row r2)).

(* Linearise a (col, row) reference into the underlying array index. *)
Definition cell_index (r : CellRef) : int :=
  PrimInt63.add (PrimInt63.mul (ref_row r) NUM_COLS) (ref_col r).

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

(* Membership check on a path of CellRefs.  Used by [eval_expr] to
   distinguish cycles (a ref already on the current evaluation path)
   from legitimate deep chains. *)
Fixpoint mem_cellref (r : CellRef) (xs : list CellRef) : bool :=
  match xs with
  | nil => false
  | y :: ys => if cellref_eqb r y then true else mem_cellref r ys
  end.

(* Total evaluator with fuel and a visited-path.

   [visited] tracks which cells the current evaluation chain has
   already entered through an [ERef].  Re-encountering a ref on
   [visited] means a cycle, so we return [None].  [fuel] is a
   generous total-termination cap; it should only ever be exhausted
   by adversarially deep expression trees.  Division by zero also
   returns [None]. *)
Fixpoint eval_expr (fuel : nat) (visited : list CellRef) (s : Sheet)
                   (e : Expr) : option Z :=
  match fuel with
  | O => None
  | S fuel' =>
    match e with
    | EInt n => Some n
    | ERef r =>
      if mem_cellref r visited then None
      else
        match get_cell s r with
        | CEmpty => Some 0%Z
        | CLit n => Some n
        | CForm e' => eval_expr fuel' (r :: visited) s e'
        end
    | EAdd a b =>
      match eval_expr fuel' visited s a, eval_expr fuel' visited s b with
      | Some va, Some vb => Some (Z.add va vb)
      | _, _ => None
      end
    | ESub a b =>
      match eval_expr fuel' visited s a, eval_expr fuel' visited s b with
      | Some va, Some vb => Some (Z.sub va vb)
      | _, _ => None
      end
    | EMul a b =>
      match eval_expr fuel' visited s a, eval_expr fuel' visited s b with
      | Some va, Some vb => Some (Z.mul va vb)
      | _, _ => None
      end
    | EDiv a b =>
      match eval_expr fuel' visited s a, eval_expr fuel' visited s b with
      | Some va, Some vb =>
        if Z.eqb vb 0%Z then None else Some (Z.div va vb)
      | _, _ => None
      end
    end
  end.

(* Evaluate a cell.  Seeds the visited path with the cell itself so
   self-references and short cycles are detected on the next [ERef]
   step. *)
Definition eval_cell (fuel : nat) (s : Sheet) (r : CellRef) : option Z :=
  match get_cell s r with
  | CEmpty => Some 0%Z
  | CLit n => Some n
  | CForm e => eval_expr fuel (r :: nil) s e
  end.

(* A generous safety cap.  Real cycles are caught by the visited-set
   check before fuel matters; fuel only stops adversarially deep
   expression trees that exhaust grid traversal budget. *)
Definition DEFAULT_FUEL : nat := 100000.

(* The smoke value: A1=2, B1=3, C1 = (A1+B1) * 7 = 35. *)
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
   the evaluator's behaviour or about set/get coherence on the
   underlying persistent array. *)

(* Reading an empty cell returns 0, regardless of fuel. *)
Theorem eval_empty : forall s r fuel,
  get_cell s r = CEmpty -> eval_cell fuel s r = Some 0%Z.
Proof. intros s r fuel H. unfold eval_cell. rewrite H. reflexivity. Qed.

(* Reading a literal cell returns the literal, regardless of fuel. *)
Theorem eval_lit : forall s r n fuel,
  get_cell s r = CLit n -> eval_cell fuel s r = Some n.
Proof. intros s r n fuel H. unfold eval_cell. rewrite H. reflexivity. Qed.

(* set/get coherence: writing a cell then reading it back returns the
   value, provided the index is in bounds for the underlying array. *)
Theorem get_set_eq : forall s r c,
  PrimInt63.ltb (cell_index r) (PrimArray.length s) = true ->
  get_cell (set_cell s r c) r = c.
Proof.
  intros s r c Hbound.
  unfold get_cell, set_cell.
  exact (@get_set_same Cell s (cell_index r) c Hbound).
Qed.

(* Frame preservation: writing one cell does not disturb a different
   cell, as long as the two refs hash to different array indices. *)
Theorem get_set_neq : forall s r1 r2 c,
  cell_index r1 <> cell_index r2 ->
  get_cell (set_cell s r2 c) r1 = get_cell s r1.
Proof.
  intros s r1 r2 c Hneq.
  unfold get_cell, set_cell.
  exact (@get_set_other Cell s (cell_index r2) (cell_index r1) c
    (fun H => Hneq (eq_sym H))).
Qed.

(* The smoke value computes to [Some 35]. *)
Theorem smoke_computes : smoke = Some 35%Z.
Proof. vm_compute. reflexivity. Qed.

(* A cell whose formula references itself is detected as a cycle and
   returns [None]. *)
Theorem eval_self_cycle_diverges :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r (CForm (ERef r)) in
  eval_cell DEFAULT_FUEL s r = None.
Proof. vm_compute. reflexivity. Qed.

(* Division by zero returns [None]. *)
Theorem eval_divzero :
  let r := mkRef 0 0 in
  let s := set_cell new_sheet r
    (CForm (EDiv (EInt 1%Z) (EInt 0%Z))) in
  eval_cell DEFAULT_FUEL s r = None.
Proof. vm_compute. reflexivity. Qed.

End Spreadsheet.
