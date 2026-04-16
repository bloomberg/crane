From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module NameClashIifeThis.

Inductive color : Type :=
| Red : color
| Green : color
| Blue : color.

Inductive shape : Type :=
| Circle : nat -> shape
| Square : nat -> nat -> shape.

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

Definition match_of_match (c : color) (s : shape) : nat :=
  match (match c with Red => Circle 5 | Green => Square 3 4 | Blue => s end) with
  | Circle r => r * 2
  | Square w h => w + h
  end.

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

End NameClashIifeThis.

Crane Extraction "name_clash_iife_this" NameClashIifeThis.
