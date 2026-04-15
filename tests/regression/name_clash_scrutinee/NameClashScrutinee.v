From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module NameClashScrutinee.

Inductive color : Type :=
| Red : color
| Green : color
| Blue : color.

Inductive shape : Type :=
| Circle : nat -> shape
| Square : nat -> nat -> shape.

(** Sequential matches on different types in the same function. *)
Definition describe (c : color) (s : shape) : nat :=
  let color_val :=
    match c with
    | Red => 1
    | Green => 2
    | Blue => 3
    end
  in
  let shape_val :=
    match s with
    | Circle r => r
    | Square w h => w + h
    end
  in
  color_val + shape_val.

(** Nested match: match on shape, and within a branch, match on color. *)
Definition nested_match (c : color) (s : shape) : nat :=
  match s with
  | Circle r =>
    match c with
    | Red => r + 10
    | Green => r + 20
    | Blue => r + 30
    end
  | Square w h =>
    match c with
    | Red => w * h
    | Green => w + h
    | Blue => 0
    end
  end.

(** Three levels of nesting. *)
Inductive wrapper : Type :=
| Wrap : color -> shape -> wrapper
| Empty : wrapper.

Definition triple_nest (w : wrapper) : nat :=
  match w with
  | Empty => 0
  | Wrap c s =>
    match s with
    | Circle r =>
      match c with
      | Red => r
      | Green => r * 2
      | Blue => r * 3
      end
    | Square w h =>
      match c with
      | Red => w + h
      | Green => w * h
      | Blue => 0
      end
    end
  end.

End NameClashScrutinee.

Crane Extraction "name_clash_scrutinee" NameClashScrutinee.
